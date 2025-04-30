(* rocq-elpi: Coq terms as the object language of elpi                       *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
module EC = API.Compile
module EPP = API.Pp
module EU = API.Utils
module ET = API.RawData

open Rocq_elpi_utils
open Rocq_elpi_arg_HOAS
module Programs = Rocq_elpi_programs

(* ******************** Vernacular commands ******************************* *)

open Programs

let default_max_step = max_int

let main_quotedc = ET.Constants.declare_global_symbol "main-quoted"
let mainc = ET.Constants.declare_global_symbol "main"
let main_interpc = ET.Constants.declare_global_symbol "main-interp"
let main_synterpc = ET.Constants.declare_global_symbol "main-synterp"
let attributesc = ET.Constants.declare_global_symbol "attributes"

let atts2impl ~depth loc phase
 state atts q =
  let open Rocq_elpi_builtins_synterp in
  let rec convert_att_r = function
    | (name,Attributes.VernacFlagEmpty) -> name, AttributeEmpty
    | (name,Attributes.VernacFlagList l) -> name, AttributeList (convert_atts l)
    | (name,Attributes.VernacFlagLeaf v) -> name, AttributeLeaf (convert_att_value v)
  and convert_att att = convert_att_r att.CAst.v
  and convert_atts l = List.map convert_att l
  and convert_att_value = function
    | Attributes.FlagIdent s [@if coq = "8.20"] -> AttributeString s
    | Attributes.FlagQualid q [@if coq <> "8.20"] -> AttributeString (Libnames.string_of_qualid q)
    | Attributes.FlagString s -> AttributeString s
  in
  let phase = match phase with Summary.Stage.Interp -> "interp" | Summary.Stage.Synterp -> "synterp" in
  let atts =
    ("elpi.loc", AttributeLeaf (AttributeLoc loc)) ::
    ("elpi.phase", AttributeLeaf (AttributeString phase)) ::
    convert_atts atts in
  let atts =
    match Sys.getenv_opt "COQ_ELPI_ATTRIBUTES" with
    | None -> atts
    | Some txt ->
        match Pcoq.parse_string (Pvernac.main_entry None) (Printf.sprintf "#[%s] Qed." txt) |> Option.map (fun x -> x.CAst.v) with
        | None -> atts
        | Some { Vernacexpr.attrs ; _ } -> List.map (fun {CAst.v=(name,v)} -> convert_att_r ("elpi."^name,v)) attrs @ atts
        | exception Gramlib.Grammar.Error msg ->
            CErrors.user_err Pp.(str"Environment variable COQ_ELPI_ATTRIBUTES contains ill formed value:" ++ spc () ++ str txt ++ cut () ++ str msg) in
  let state, atts, _ = EU.map_acc (Rocq_elpi_builtins_synterp.attribute.API.Conversion.embed ~depth) state atts in
  let atts = ET.mkApp attributesc (EU.list_to_lp_list atts) [] in
  state, ET.mkBuiltin ET.Impl [atts;q] 

let same_phase y x =
  match x, y with
  | _, Both -> true
  | Summary.Stage.Interp, Interp -> true
  | Summary.Stage.Synterp, Synterp -> true
  | _ -> false

let skip ?only ~ph ~phase f x =
  let m rex = Str.string_match rex Coq_config.version 0 in
  let exec1 =
    match only with
    | None -> true
    | Some (None, None) -> true
    | Some (Some skip, None) -> not (List.exists m skip)
    | Some (None, Some keep) -> List.exists m keep
    | Some (Some _, Some _) -> CErrors.user_err Pp.(str "Attributes #[skip] and #[only] cannot be used at the same time")
  in
  let exec2 =
    match ph with
    | None -> same_phase Interp phase
    | Some ph -> same_phase ph phase
  in
    if exec1 && exec2 then f x else ()

type query =
  | Ast of (API.Data.state -> API.Data.state) * API.Ast.query
  | Fun of (API.Data.state -> API.Data.state * API.RawData.term * Elpi.API.Conversion.extra_goals)

type atts = ((clause_scope * (Str.regexp list option * Str.regexp list option)) * phase option)
type what = Code | Signature

let warn_scope_not_regular = CWarnings.create ~name:"elpi.accumulate-scope" ~category:elpi_cat (fun x -> x)
let warn_scope_not_regular ~loc = function
  | Regular -> ()
  | _ -> warn_scope_not_regular ~loc Pp.(str "Scope attribute not supported, this accumulation has a superglobal scope")

module Compiler(P : Programs) = struct

  module Summary = struct
    include Summary
    let ref ?local ~name x = Summary.ref ~stage:P.stage ?local ~name:(P.in_stage name) x
  end

  let skip = skip ~phase:P.stage

  let trace_options = Summary.ref ~name:"elpi-trace" []
  let max_steps = Summary.ref ~name:"elpi-steps" default_max_step

  let debug vl = P.debug_vars := List.fold_right EC.StrSet.add vl EC.StrSet.empty
  let debug ~atts:ph vl = skip ~ph debug vl

  let bound_steps n =
    if n <= 0 then max_steps := default_max_step else max_steps := n
  let bound_steps ~atts:ph n = skip ~ph bound_steps n

let trace_filename_gen (add_counter: string) =
  "/tmp/traced.tmp" ^ (add_counter) ^ ".json"

let trace_filename = trace_filename_gen ""

let run ~loc program query =
  let t1 = Unix.gettimeofday () in

  let query =
    handle_elpi_compiler_errors ~loc (fun () ->
    match query with
    | Ast (f,query_ast) -> API.RawQuery.compile_ast program query_ast f
    | Fun query_builder -> API.RawQuery.compile_raw_term program query_builder) in
  let t2 = Unix.gettimeofday () in
  let _ = API.Setup.trace [] in
  let t3 = Unix.gettimeofday () in
  let leftovers = API.Setup.trace !trace_options in
  if (!trace_options <> [] && Sys.file_exists trace_filename) then 
    Sys.command (Printf.sprintf "mv %s %s" trace_filename (trace_filename_gen (Printf.sprintf "_%.0f" @@ Unix.gettimeofday ()))) |> ignore;
  if leftovers <> [] then
    CErrors.user_err Pp.(str"Unknown trace options: " ++ prlist_with_sep spc str leftovers);
  let exe = EC.optimize query in
  let t4 = Unix.gettimeofday () in
  let print_debug with_error = 
    let t5 = Unix.gettimeofday () in
    let txt = Printf.sprintf "Elpi: query-compilation:%1.4f static-check:%1.4f optimization:%1.4f runtime:%1.4f %s\n"
        (t2 -. t1) (t3 -. t2) (t4 -. t3) (t5 -. t4) (if with_error then "(with error)" else "(with success)") in
    Rocq_elpi_utils.debug Pp.(fun () -> str txt);
    Rocq_elpi_utils.elpitime Pp.(fun () -> str txt)
  in
  try
    let rc = API.Execute.once ~max_steps:!max_steps exe in
    print_debug false;
    rc
  with e ->
    let e = Exninfo.capture e in
    print_debug true;
    Exninfo.iraise e
;;

let elpi_fails program_name =
  let open Pp in
  let kind = "tactic/command" in
  let name = show_qualified_name program_name in
  CErrors.user_err (strbrk (String.concat " " [
    "The elpi"; kind; name ;
    "failed without giving a specific error message" ^ (Summary.Stage.(match P.stage with Interp -> "." | Synterp -> " (during the parsing phase, aka synterp)."));
    "Please report this inconvenience to the authors of the program."
  ]))
   
let run_and_print ~print ~loc program_name program_ast query_ast : _ * Rocq_elpi_builtins_synterp.SynterpAction.RZipper.zipper =
  let open API.Data in let open Rocq_elpi_utils in
  match run ~loc program_ast query_ast
  with
  | API.Execute.Failure -> elpi_fails program_name
  | API.Execute.NoMoreSteps ->
      CErrors.user_err Pp.(str "elpi run out of steps ("++int !max_steps++str")")
  | API.Execute.Success {
    assignments ; constraints; state; pp_ctx; relocate_assignment_to_runtime;
    } ->
    if print then begin
      if not (StrMap.is_empty assignments) then begin
        Feedback.msg_notice
          Pp.(str"Query assignments:");
        StrMap.iter (fun name term ->
          Feedback.msg_notice
            Pp.(str"  " ++ str name ++ str " = " ++
                str (pp2string (EPP.term pp_ctx) term)))
          assignments;
        end;
      let scst = pp2string (EPP.constraints pp_ctx) constraints in
      if scst <> "" then
        Feedback.msg_notice Pp.(str"Syntactic constraints:" ++ spc()++str scst);
      if P.stage = Summary.Stage.Interp then begin
        let sigma = Rocq_elpi_HOAS.get_sigma state in
        let ccst = Evd.evar_universe_context sigma in
        if not (UState.is_empty ccst) then
          Feedback.msg_notice Pp.(str"Universe constraints:" ++ spc() ++
            Termops.pr_evar_universe_context ccst);
      end
    end;
    (* We add clauses declared via coq.elpi.accumulate *)
    let clauses_to_add =
      API.State.get
        (match P.stage with
        | Summary.Stage.Synterp -> Rocq_elpi_builtins_synterp.clauses_for_later_synterp
        | Summary.Stage.Interp  -> Rocq_elpi_builtins.clauses_for_later_interp)
        state in

    (* TODO: this code is duplicate, see set_accumulate_to_db_* *)
    let elpi = P.ensure_initialized () in
    let clauses_to_add = clauses_to_add |> group_clauses |>
      List.map (fun (dbname,asts,vs,scope) ->
        let base = P.get_and_compile_existing_db ~loc dbname in
        (* maybe this should be a fold otherwise all clauses have to be independent (the second cannot mention the first one) *)
        let units = asts |> List.map (fun ast -> P.unit_from_ast ~error_header:(Format.asprintf "accumulating clause to %s" (String.concat "." dbname)) ~elpi None ~base ~loc (EC.scope ~elpi ast)) in
      dbname,units,vs,scope) in
    clauses_to_add |> List.iter (fun (dbname,units,vs,scope) ->
      P.accumulate_to_db dbname units vs ~scope);
    relocate_assignment_to_runtime,
    if P.stage = Summary.Stage.Synterp then
      API.State.get Rocq_elpi_builtins_synterp.SynterpAction.log state |> Rocq_elpi_builtins_synterp.SynterpAction.RZipper.of_w
    else API.State.get Rocq_elpi_builtins_synterp.SynterpAction.read state

let current_program = Summary.ref ~name:"elpi-cur-program-name" None
let set_current_program n =
  current_program := Some n
  
let current_program () =
  match !current_program with
  | None -> CErrors.user_err Pp.(str "No current Elpi Program")
  | Some x -> x

let get_base ~loc ~elpi program : [ `Program of EC.program | `Db of EC.program ]=
  if P.db_exists program then
    `Db (P.get_and_compile_existing_db ~loc program)
  else
    match P.get_and_compile ~loc ~even_if_empty:true program with
    | None -> CErrors.user_err ~loc Pp.(str "Unknown program " ++ pr_qualified_name program)
    | Some (base, _) -> `Program base

let run_in_program ~loc ?(program = current_program ()) ?(st_setup=fun _ x -> x) (qloc, query) =
  let elpi = P.ensure_initialized () in
  P.get_and_compile ~loc ~even_if_empty:true program |> Option.map (fun (base, _) ->
    let query_ast = Ast (st_setup base, P.parse_goal ~loc ~elpi qloc query) in
    run_and_print ~print:true ~loc program base query_ast)

  let accumulate_extra_deps ~loc ?(program=current_program()) ~scope ~what ids =
    let elpi = P.ensure_initialized () in
    let () = ids |> List.iter (fun id ->
      let base = get_base ~loc ~elpi program in
      let base, add =
        match base with
        | `Db base -> base, (fun _ fast -> P.accumulate_to_db program [fast] [] ~scope)
        | `Program base -> base, (fun fname fast ->
           warn_scope_not_regular ~loc scope;
           P.accumulate program [File { fname; fast}]) in
      let cid = Names.Id.of_string_soft (String.concat "." id) in
      let s, u =
        try
          let s = ComExtraDeps.query_extra_dep cid in
          s, match what with
             | Code -> P.unit_from_file ~elpi ~loc ~base s
             | Signature -> P.unit_signature_from_file ~elpi ~loc ~base s
        with
        | Failure s ->  CErrors.user_err ~loc Pp.(str s)
        | Not_found ->
          try
            let hash, ast = P.ast_of_file id in
            String.concat "." id,
              match what with
              | Code -> P.unit_from_ast ~elpi ~base ~loc (Some hash) ast
              | Signature -> P.unit_signature_from_ast ~elpi ~base ~loc (Some hash) ast
          with
          | Failure s ->  CErrors.user_err Pp.(str s)
          | Not_found when P.stage = Summary.Stage.Interp ->
              CErrors.user_err ~loc Pp.(str"File " ++ Names.Id.print cid ++ str " not found")
          | Not_found ->
              err Pp.(str"File " ++ pr_qualified_name id ++
                str" is unknown; please add a directive like 'From .. Extra Dependency .. as " ++
                pr_qualified_name id ++ str"' or 'Elpi File .. lp:{{ ... }}'.")
      in
         add s u)
    in
    ()
    
  let accumulate_extra_deps ~atts:((scope,only),ph) ~loc ?program ~what ids = skip ~only ~ph (accumulate_extra_deps ~loc ?program ~scope ~what) ids

  let accumulate_files ~loc ?(program=current_program()) ~scope s =
    let elpi = P.ensure_initialized () in
    try
      match get_base ~loc ~elpi program with
      | `Db base ->
        let new_src_ast = List.map (fun fname -> P.unit_from_file ~loc ~elpi ~base fname) s in
        P.accumulate_to_db program new_src_ast [] ~scope
      | `Program base ->
        warn_scope_not_regular ~loc scope;
        let new_src_ast = List.map (fun fname -> P.unit_from_file ~loc ~elpi ~base fname) s in
        let new_src_ast = List.map2 (fun fname funit ->
          File {
            fname;
            fast = funit;
          }) s new_src_ast in
        P.accumulate program new_src_ast
    with Failure s ->  CErrors.user_err Pp.(str s)
  let accumulate_files ~atts:((scope,only),ph) ~loc ?program s = skip ~only ~ph (accumulate_files ~loc ?program ~scope) s
  
  let accumulate_string ~loc ?(program=current_program()) ~scope (sloc,s) =
    let elpi = P.ensure_initialized () in
    match get_base ~elpi ~loc program with
    | `Db base ->
      let new_ast = P.unit_from_string ~elpi ~base ~loc sloc s in
      P.accumulate_to_db program [new_ast] [] ~scope
    | `Program base ->
      warn_scope_not_regular ~loc scope;
      let new_ast = P.unit_from_string ~elpi ~base ~loc sloc s in
      P.accumulate program [EmbeddedString { sast = new_ast}]
  let accumulate_string ~atts:((scope,only),ph) ~loc ?program sloc = skip ~only ~ph (accumulate_string ~loc ?program ~scope) sloc
  
  
  let accumulate_db ~loc ?(program=current_program()) name =
    let _ = P.ensure_initialized () in
    let header = P.header_of_db name |> List.map (fun dast -> DatabaseHeader { dast }) in
    if P.db_exists name then P.accumulate program (header @ [DatabaseBody name])
    else CErrors.user_err Pp.(str "Db " ++ pr_qualified_name name ++ str" not found")
  let accumulate_db ~atts:((scope,only),ph) ~loc ?program name =
    warn_scope_not_regular ~loc scope;
    skip ~only ~ph (accumulate_db ~loc ?program) name
  
  let accumulate_db_header ~loc ?(program=current_program()) ~scope name =
    let _ = P.ensure_initialized () in
    if P.db_exists name then
      let units = P.header_of_db name in
      if P.db_exists program then
        P.accumulate_to_db program units [] ~scope
      else
        let () = warn_scope_not_regular ~loc scope in
        let units = List.map (fun dast -> DatabaseHeader { dast }) units in
        P.accumulate program units
    else CErrors.user_err Pp.(str "Db " ++ pr_qualified_name name ++ str" not found")
  let accumulate_db_header ~atts:((scope,only),ph) ~loc ?program name =
    skip ~only ~ph (accumulate_db_header ~loc ?program ~scope) name
  
  let accumulate_to_db ~loc db (sloc,s) ~scope idl =
    let elpi = P.ensure_initialized () in
    match get_base ~elpi ~loc db with
    | `Db base ->
       let new_ast = P.unit_from_string ~elpi ~base ~loc sloc s in
       P.accumulate_to_db db [new_ast] idl ~scope
    | _ -> CErrors.user_err Pp.(str "Db " ++ pr_qualified_name db ++ str" not found") 
  let accumulate_to_db ~atts:((scope,only),ph) ~loc db sloc idl = skip ~only ~ph (accumulate_to_db ~loc db sloc ~scope) idl
  

  let mk_trace_opts start stop preds =
    [ "-trace-on"
    ; "-trace-at"; "run"; string_of_int start; string_of_int stop
    ; "-trace-only"; "\\(run\\|select\\|user:\\)"
    ; "-trace-tty-maxbox"; "30"
    ] @ List.(flatten (map (fun x -> ["-trace-only-pred"; x]) preds))
  
  let trace start stop preds opts =
    if start = 0 && stop = 0 then trace_options := []
    else trace_options := mk_trace_opts start stop preds @ opts
  let trace ~atts start stop preds opts = skip ~ph:atts (trace start stop preds) opts
  
  let trace_browser _opts =
    trace_options :=
      [ "-trace-on"; "json"; trace_filename
      ; "-trace-at"; "run"; "0"; string_of_int max_int
      ; "-trace-only"; "user"
      ];
    Feedback.msg_notice
      Pp.(strbrk "Now click \"Start watching\" in the Elpi Trace Browser panel and then execute the Command/Tactic/Query you want to trace. Also try \"F1 Elpi\".")
  let trace_browser ~atts opts = skip ~ph:atts trace_browser opts
      
  let print ~loc ~name ~args output =
    let program =
      if P.db_exists name then
        Some (P.get_and_compile_existing_db ~loc name)
      else
        Option.map fst @@ P.get_and_compile ~loc name in
    program |> Option.iter @@ fun program ->
    let fname =
      Rocq_elpi_programs.resolve_file_path
        ~must_exist:false ~allow_absolute:false ~only_elpi:false output
    in
    let fname_txt = fname ^ ".txt" in
    let oc = open_out fname_txt in
    let fmt = Format.formatter_of_out_channel oc in
    EPP.program fmt program;
    Format.pp_print_flush fmt ();
    close_out oc
  let print ~atts ~loc ~name ~args output =
    skip ~ph:atts (print ~loc ~name ~args) output

  let create_command ~atts:(raw_args) ~loc:_ n =
    let raw_args = Option.default false raw_args in
    let _ = P.ensure_initialized () in
    P.declare_program n (Command { raw_args });
    P.init_program n [P.command_init()];
    set_current_program (snd n)

  let create_tactic ~loc:_ n =
    let _ = P.ensure_initialized () in
    P.declare_program n Tactic;
    if P.stage = Summary.Stage.Interp then P.init_program n [P.command_init();P.tactic_init ()];
    set_current_program (snd n)

  let create_program ~atts:(raw_args) ~loc n ~init:(sloc,s) =
    let raw_args = Option.default false raw_args in
    let elpi = P.ensure_initialized () in
    P.declare_program n (Program { raw_args });
    if P.stage = Summary.Stage.Interp then begin
      let unit = P.unit_from_string ~elpi ~base:(EC.empty_base ~elpi) ~loc sloc s in
      let init = EmbeddedString { sast = unit} in
      P.init_program n [init];
    end;
    set_current_program (snd n)

  let create_db ~atts ~loc n ~init:(sloc,s) =
    let do_init =
      match atts with
      | None -> same_phase Interp P.stage
      | Some phase -> same_phase phase P.stage in
    if do_init then begin
      P.declare_db n;
      P.init_db n ~loc (sloc,s)  
    end

  let create_file ~atts ~loc n ~init:(sloc,s) =
    let do_init =
      match atts with
      | None -> same_phase Interp P.stage
      | Some phase -> same_phase phase P.stage in
    let elpi = P.ensure_initialized () in
    if do_init then begin
      P.declare_file n;
      P.init_file n P.(ast_from_string ~elpi ~loc sloc s)
    end

  let load_command = P.load_command
  let load_tactic = P.load_tactic
  
  let get_and_compile ~loc qn = P.get_and_compile ?even_if_empty:None qn ~loc

end

module type Common = sig
  val get_and_compile :
    loc:Loc.t -> qualified_name -> (Elpi.API.Compile.program * bool) option
  val run : loc:Loc.t ->
    Elpi.API.Compile.program ->
     query ->
    Elpi.API.Execute.outcome  

  val accumulate_files       : atts:atts -> loc:Loc.t -> ?program:qualified_name -> string list -> unit
  val accumulate_extra_deps  : atts:atts -> loc:Loc.t -> ?program:qualified_name -> what:what -> qualified_name list -> unit
  val accumulate_string      : atts:atts -> loc:Loc.t -> ?program:qualified_name -> Elpi.API.Ast.Loc.t * string -> unit
  val accumulate_db          : atts:atts -> loc:Loc.t -> ?program:qualified_name -> qualified_name -> unit
  val accumulate_db_header   : atts:atts -> loc:Loc.t -> ?program:qualified_name -> qualified_name -> unit
  val accumulate_to_db       : atts:atts -> loc:Loc.t -> qualified_name -> Elpi.API.Ast.Loc.t * string -> Names.Id.t list -> unit
  val load_tactic : loc:Loc.t -> string -> unit
  val load_command : loc:Loc.t -> string -> unit

  val debug         : atts:phase option -> string list -> unit
  val trace         : atts:phase option -> int -> int -> string list -> string list -> unit
  val trace_browser : atts:phase option -> string list -> unit
  val bound_steps   : atts:phase option -> int -> unit
  val print         : atts:phase option -> loc:Loc.t -> name:qualified_name -> args:string list -> string -> unit

  val create_program : atts:bool option -> loc:Loc.t -> program_name -> init:(Elpi.API.Ast.Loc.t * string) -> unit
  val create_command : atts:bool option -> loc:Loc.t -> program_name -> unit
  val create_tactic : loc:Loc.t -> program_name -> unit
  val create_db : atts:phase option -> loc:Loc.t -> program_name -> init:(Elpi.API.Ast.Loc.t * string) -> unit
  val create_file : atts:phase option -> loc:Loc.t -> program_name -> init:(Elpi.API.Ast.Loc.t * string) -> unit

end

module Synterp = struct
  include Compiler(Rocq_elpi_programs.Synterp)

  let main_syterp args syndata =
    ET.mkApp API.RawData.Constants.orc
      (ET.mkApp main_synterpc (EU.list_to_lp_list args) [syndata])
      [ET.mkApp mainc (EU.list_to_lp_list args) []]
  
  let run_program ~loc name ~atts args =
    get_and_compile ~loc name |> Option.map (fun (program, raw_args) ->
      let initial_synterp_state = Vernacstate.Synterp.freeze () in
      let query state =
        let loc = Rocq_elpi_utils.of_coq_loc loc in
        let depth = 0 in
        let state, args, gls = EU.map_acc
          (Rocq_elpi_arg_HOAS.in_elpi_cmd_synterp ~depth)
          state args in
        let state, ek = API.FlexibleData.Elpi.make ~name:"NewData" state in
        let data = ET.mkUnifVar ek ~args:[] state in
        let state, q = atts2impl loc Summary.Stage.Synterp ~depth state atts (main_syterp args data) in
        let state = API.State.set Rocq_elpi_builtins_synterp.invocation_site_loc_synterp state loc in
        state, q, gls in
      try
        let relocate, synterplog = run_and_print ~loc ~print:false name program (Fun query) in
        initial_synterp_state, relocate "NewData", synterplog
      with Rocq_elpi_builtins_synterp.SynterpAction.Error x -> err x)

  let run_in_program ~loc ?program query =
    try run_in_program ~loc ?program query |> Option.map (fun (_,x) -> x)
    with Rocq_elpi_builtins_synterp.SynterpAction.Error x -> err x
    
end

let document_builtins = document_builtins

module Interp = struct

  include Compiler(Rocq_elpi_programs.Interp)

  let main_interp args syndata =
    ET.mkApp API.RawData.Constants.orc
     (ET.mkApp main_interpc (EU.list_to_lp_list args) [syndata])
     [ET.mkApp mainc (EU.list_to_lp_list args) []]
    
  let missing_synterp = let open Pp in
    fnl() ++
    strbrk "The command lacks code for the synterp phase. In order to add code to this phase use '#[synterp] Elpi Accumulate'. See also https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_command.html#parsing-and-execution"
  
  let run_program ~loc name ~atts ~syndata args =
    get_and_compile ~loc name |> Option.iter (fun (program, raw_args) ->
      let env = Global.env () in
      let sigma = Evd.from_env env in
      let args = args
        |> List.map (Rocq_elpi_arg_HOAS.Cmd.glob (Genintern.empty_glob_sign ~strict:true env))
        |> List.map (Rocq_elpi_arg_HOAS.Cmd.interp (Ltac_plugin.Tacinterp.default_ist ()) env sigma)
      in
      let initial_synterp_state, synterplog, synterm =
        match syndata with
        | None ->
          let initial_synterp_state = Vernacstate.Synterp.freeze () in
          initial_synterp_state,
          Rocq_elpi_builtins_synterp.SynterpAction.RZipper.empty,
          fun ~target:_ ~depth -> Stdlib.Result.Ok ET.mkDiscard
        | Some (initial_synterp_state,relocate_term,log) -> initial_synterp_state, log, relocate_term in
      let query state =
        let depth = 0 in
        let state, args, gls = EU.map_acc
          (Rocq_elpi_arg_HOAS.in_elpi_cmd ~loc ~depth ~base:program ~raw:raw_args Rocq_elpi_HOAS.(mk_coq_context ~options:(default_options ()) state))
          state args in
        let loc = Rocq_elpi_utils.of_coq_loc loc in
        let synterm =
          match synterm ~target:program ~depth with
          | Stdlib.Result.Ok x -> x
          | Stdlib.Result.Error s -> err Pp.(str"Data returned by the synterp phase cannot be passed to the interp phase due to unknown symbol: " ++ str s) in
          
        let state, q = atts2impl loc Summary.Stage.Interp ~depth state atts (main_interp args synterm) in
        let state = API.State.set Rocq_elpi_builtins.base state (Some program) in
        let state = API.State.set Rocq_elpi_builtins.tactic_mode state false in
        let state = API.State.set Rocq_elpi_builtins_synterp.invocation_site_loc state loc in
        let state = API.State.set Rocq_elpi_builtins_synterp.SynterpAction.read state synterplog in
        state, q, gls in
      let final_synterp_state = Vernacstate.Synterp.freeze () in
      Vernacstate.Synterp.unfreeze initial_synterp_state;
      try begin
        try 
            let _, synterp_left = run_and_print ~loc ~print:false name program (Fun query) in
            match Rocq_elpi_builtins_synterp.SynterpAction.RZipper.is_empty synterp_left with
            | `Empty -> Vernacstate.Synterp.unfreeze final_synterp_state
            | `Group g ->
                let g = Rocq_elpi_builtins_synterp.SynterpAction.Tree.group_name g in
                err Pp.(strbrk"The execution phase did not consume all the parse time actions. Next in the queue is group " ++ str g)
            | `Action a ->
                err Pp.(strbrk"The execution phase did not consume all the parse time actions. Next in the queue is action " ++ Rocq_elpi_builtins_synterp.SynterpAction.pp a)
        with
        | Rocq_elpi_builtins_synterp.SynterpAction.Error x when syndata = None ->
            err Pp.(x ++ missing_synterp)
        | Rocq_elpi_builtins_synterp.SynterpAction.Error x ->
            err x
      end with e ->
        let e = Exninfo.capture e in
        Vernacstate.Synterp.unfreeze final_synterp_state;
        (match fst e with
         | CErrors.UserError _ -> ()
         | _ -> Feedback.msg_debug Pp.(str "elpi lets escape exception: " ++ CErrors.iprint e));
        Exninfo.iraise e)
  
  let run_in_program ~loc ?program ~syndata query =
    let st_setup base state =
      let syndata = Option.default (Rocq_elpi_builtins_synterp.SynterpAction.RZipper.empty) syndata in
      let state = API.State.set Rocq_elpi_builtins.base state (Some base) in
      API.State.set Rocq_elpi_builtins_synterp.SynterpAction.read state syndata in
    try ignore @@ run_in_program ~loc ?program ~st_setup query
    with
    | Rocq_elpi_builtins_synterp.SynterpAction.Error x when syndata = None -> err Pp.(x ++ missing_synterp)
    | Rocq_elpi_builtins_synterp.SynterpAction.Error x -> err x

            
end

open Tacticals

let run_tactic_common ~loc program ~main ?(atts=[]) () =
  let open Proofview in
  let open Notations in
  let open Interp in
  Unsafe.tclGETGOALS >>= fun gls ->
  let gls = CList.map Proofview.drop_state gls in
  Proofview.tclEVARMAP >>= fun sigma ->
  let query ~base state =
    let loc = of_coq_loc loc in
    let depth = 0 in
    let state, main_query, gls = main ~base sigma gls state in
    let state, main_query = atts2impl ~depth loc Summary.Stage.Interp state atts main_query in
    let state = API.State.set Rocq_elpi_builtins.tactic_mode state true in
    let state = API.State.set Rocq_elpi_builtins_synterp.invocation_site_loc state loc in
    state, main_query, gls
    in
  get_and_compile ~loc program |> Option.cata (fun (cprogram, _) ->
    match run ~loc cprogram (Fun (query ~base:cprogram)) with
    | API.Execute.Success solution -> Rocq_elpi_HOAS.tclSOLUTION2EVD ~eta_contract_solution:false sigma solution
    | API.Execute.NoMoreSteps -> CErrors.user_err Pp.(str "elpi run out of steps")
    | API.Execute.Failure -> elpi_fails program
    | exception (Rocq_elpi_utils.LtacFail (level, msg)) -> tclFAILn level msg
    | exception (CErrors.UserError _ as e) -> let e = Exninfo.capture e in Exninfo.iraise e
    | exception e when CErrors.noncritical e -> let e = Exninfo.capture e in (Feedback.msg_debug Pp.(str "elpi lets escape exception: " ++ CErrors.iprint e); Exninfo.iraise e))
  tclIDTAC

let run_tactic ~loc program ~atts _ist args =
  run_tactic_common ~loc program ~atts ~main:(fun ~base sigma gls state ->
    Rocq_elpi_HOAS.solvegoals2query sigma gls (Rocq_elpi_utils.of_coq_loc loc) ~main:args ~base
        ~in_elpi_tac_arg:Rocq_elpi_arg_HOAS.(in_elpi_tac ~loc) ~depth:0 state) ()

let run_in_tactic ~loc ?(program = Interp.current_program ()) (qloc,query) _ist =
  run_tactic_common ~loc program ~main:(fun ~base sigma gls state ->
    Rocq_elpi_HOAS.txtgoals2query sigma gls qloc ~main:query ~base ~depth:0 state)
  ()

let loc_merge l1 l2 =
  try Loc.merge l1 l2
  with Failure _ -> l1

let cache_program (nature,p,q) =
  let p_str = String.concat "." q in
  match nature with
  | Command _ ->
    let command = Vernacexpr.{
      ext_plugin = "rocq-elpi.elpi";
      ext_entry = "Elpi" ^ p_str;
      ext_index = 0;
    } in
    let ext =
      Vernacextend.declare_dynamic_vernac_extend
        ~command
        ?entry:None
        ~depr:false

        (fun _loc0 _args _loc1 -> (Vernacextend.VtSideff ([], VtNow)))

        (Vernacextend.TyNonTerminal
           (Extend.TUentry
              (Genarg.get_arg_tag Rocq_elpi_arg_syntax.wit_elpi_loc),
            Vernacextend.TyTerminal
              (p_str,
               Vernacextend.TyNonTerminal
                 (Extend.TUlist0
                    (Extend.TUentry (Genarg.get_arg_tag Rocq_elpi_arg_syntax.wit_elpi_cmd_arg))
                 ,Vernacextend.TyNonTerminal
                     (Extend.TUentry (Genarg.get_arg_tag Rocq_elpi_arg_syntax.wit_elpi_loc),
                      Vernacextend.TyNil)))))

        (fun loc0 args loc1 ?loc ~atts () ->
          let loc = Option.default (loc_merge loc0 loc1) loc in
          let syndata = Synterp.run_program ~loc p ~atts args in
          Vernactypes.vtdefault (fun () ->
             Interp.run_program ~loc p ~atts ~syndata args))
    in
    Egramml.extend_vernac_command_grammar ~undoable:true ext

  | Tactic ->
    Rocq_elpi_builtins.cache_tac_abbrev ~code:p ~name:q
  | Program _ ->
    CErrors.user_err Pp.(str "elpi: Only commands and tactics can be exported")

let subst_program = function
  | _, (Command _,_,_) -> CErrors.user_err Pp.(str"elpi: No functors yet")
  | _, (Tactic,_,_ as x) -> x
  | _, (Program _,_,_) -> assert false

let in_exported_program : nature * qualified_name * qualified_name -> Libobject.obj =
  let open Libobject in
  declare_object @@ { (global_object_nodischarge "ELPI-EXPORTED"
    ~cache:cache_program
    ~subst:(Some subst_program)) with object_stage = Summary.Stage.Synterp }

let export_command ?as_ p =
  let q =
    match as_ with
    | None -> p
    | Some x -> x in
  let nature = Rocq_elpi_programs.Synterp.get_nature p in
  Lib.add_leaf (in_exported_program (nature,p,q))

