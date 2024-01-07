(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
module EC = API.Compile
module EPP = API.Pp
module EU = API.Utils
module ET = API.RawData

open Coq_elpi_utils
open Coq_elpi_arg_HOAS
module Programs = Coq_elpi_programs

(* ******************** Vernacular commands ******************************* *)

open Programs

let default_max_step = max_int

let main_quotedc = ET.Constants.declare_global_symbol "main-quoted"
let mainc = ET.Constants.declare_global_symbol "main"
let main_interpc = ET.Constants.declare_global_symbol "main-interp"
let main_synterpc = ET.Constants.declare_global_symbol "main-synterp"
let attributesc = ET.Constants.declare_global_symbol "attributes"

let atts2impl loc phase ~depth state atts q =
  let open Coq_elpi_builtins_synterp in
  let rec convert_att_r = function
    | (name,Attributes.VernacFlagEmpty) -> name, AttributeEmpty
    | (name,Attributes.VernacFlagList l) -> name, AttributeList (convert_atts l)
    | (name,Attributes.VernacFlagLeaf v) -> name, AttributeLeaf (convert_att_value v)
  and convert_att att = convert_att_r att.CAst.v
  and convert_atts l = List.map convert_att l
  and convert_att_value = function
    Attributes.FlagIdent s | Attributes.FlagString s -> AttributeString s
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
  let state, atts, _ = EU.map_acc (Coq_elpi_builtins_synterp.attribute.API.Conversion.embed ~depth) state atts in
  let atts = ET.mkApp attributesc (EU.list_to_lp_list atts) [] in
  state, ET.mkApp ET.Constants.implc atts [q] 

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

(* Units are marshalable, but programs are not *)

let compiler_cache_code = Summary.ref ~local:true
  ~name:("elpi-compiler-cache-code")
  Int.Map.empty
let compiler_cache_chunk = Summary.ref ~local:true
  ~name:("elpi-compiler-cache-chunk")
  Int.Map.empty

let programs_tip = Summary.ref ~local:true
  ~name:("elpi-compiler-cache-gc")
  SLMap.empty

(* lookup/cache for hash h shifted over base b *)

let lookup b h src r cmp =
  let h = combine_hash b h in
  let p, src' = Int.Map.find h !r in
  if cmp src src' then p else assert false

let cache b h prog src r =
  let h = combine_hash b h in
  r := Int.Map.add h (prog,src) !r;
  prog

let uncache b h r =
  let h = combine_hash b h in
  r := Int.Map.remove h !r
    
let lookup_code b h src = lookup b h src compiler_cache_code (Code.eq Chunk.eq)
let lookup_chunk b h src = lookup b h src compiler_cache_chunk Chunk.eq

let cache_code b h prog src = cache b h prog src compiler_cache_code
let cache_chunk b h prog src = cache b h prog src compiler_cache_chunk
  
let recache_code b h1 h2 p src =
  uncache b h1 compiler_cache_code;
  cache_code b h2 p src

let recache_chunk b h1 h2 p src =
  uncache b h1 compiler_cache_chunk;
  cache_chunk b h2 p src

let compile src =
  let rec compile_code src =
    let h = Code.hash src in
    try
      lookup_code 0 h src
    with Not_found ->
      match src with
      | Code.Base { base = (k,u) } ->
          let elpi = P.ensure_initialized () in
          let prog = P.assemble_units ~elpi [u] in
          cache_code 0 h prog src
      | Code.Snoc { prev; source } ->
          let base = compile_code prev in
          let prog = P.extend_w_units ~base [snd source] in
          if Code.cache src then cache_code 0 h prog src else prog
      | Code.Snoc_db { prev; chunks } ->
          let base = compile_code prev in
          let prog = compile_chunk (Code.hash prev) base chunks in
          prog
  and compile_chunk bh base src =
    (* DBs have to be re-based on top of base, hence bh *)
    let h = Chunk.hash src in
    try
      lookup_chunk bh h src
    with Not_found ->
      match src with
      | Chunk.Base { base = (k,u) } ->
          let prog = P.extend_w_units ~base [u] in
          cache_chunk bh h prog src
      | Chunk.Snoc { prev; source_rev } ->
          let base = compile_chunk bh base prev in
          let prog = P.extend_w_units ~base (List.rev_map snd source_rev) in
          recache_chunk bh (Chunk.hash prev) h prog src
  in
    compile_code src

let get_and_compile ?even_if_empty name : (EC.program * bool) option =
  P.code ?even_if_empty name |> Option.map (fun src ->
    let prog = compile src in
    let new_hash = Code.hash src in
    let old_hash = try SLMap.find name !programs_tip with Not_found -> 0 in
    programs_tip := SLMap.add name new_hash !programs_tip;
    let prog = recache_code 0 old_hash new_hash prog src in
    let raw_args =
      match P.get_nature name with
      | Command { raw_args } -> raw_args
      | Program { raw_args } -> raw_args
      | Tactic -> true in
    (prog, raw_args))

let run_static_check query =
  let checker = 
    let elpi = P.ensure_initialized () in
    P.assemble_units ~elpi (P.checker()) in
  (* We turn a failure into a proper error in etc/coq-elpi_typechecker.elpi *)
  ignore (EC.static_check ~checker query)

let trace_counter = ref 0
let trace_filename_gen (add_counter: string) =
  "/tmp/traced.tmp" ^ (add_counter) ^ ".json"

let trace_filename = trace_filename_gen ""

let run ~static_check program query =
  let t1 = Unix.gettimeofday () in
  let query =
    match query with
    | `Ast (f,query_ast) -> API.RawQuery.compile_ast program query_ast f
    | `Fun query_builder -> API.RawQuery.compile program query_builder in
  let t2 = Unix.gettimeofday () in
  let _ = API.Setup.trace [] in
  if static_check then run_static_check query;
  let t3 = Unix.gettimeofday () in
  let leftovers = API.Setup.trace !trace_options in
  if (!trace_options <> [] && Sys.file_exists trace_filename) then 
    Sys.command (Printf.sprintf "mv %s %s" trace_filename (trace_filename_gen (Printf.sprintf "_%d" !trace_counter))) |> ignore;
  if leftovers <> [] then
    CErrors.user_err Pp.(str"Unknown trace options: " ++ prlist_with_sep spc str leftovers);
  let exe = EC.optimize query in
  let t4 = Unix.gettimeofday () in
  let rc = API.Execute.once ~max_steps:!max_steps exe in
  let t5 = Unix.gettimeofday () in
  Coq_elpi_utils.debug Pp.(fun () ->
      str @@ Printf.sprintf
        "Elpi: query-compilation:%1.4f static-check:%1.4f optimization:%1.4f runtime:%1.4f\n"
        (t2 -. t1) (t3 -. t2) (t4 -. t3) (t5 -. t4));
  rc
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
   
let run_and_print ~print ~static_check program_name program_ast query_ast : _ * Coq_elpi_builtins_synterp.SynterpAction.t list =
  let open API.Data in let open Coq_elpi_utils in
  match run ~static_check program_ast query_ast
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
        let sigma = Coq_elpi_HOAS.get_sigma state in
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
        | Summary.Stage.Synterp -> Coq_elpi_builtins_synterp.clauses_for_later_synterp
        | Summary.Stage.Interp  -> Coq_elpi_builtins.clauses_for_later_interp)
        state in
    let elpi = P.ensure_initialized () in
    let flags = P.cc_flags() in
    let clauses_to_add = clauses_to_add |> group_clauses |>
      List.map (fun (dbname,asts,vs,scope) ->
      let units = asts |> List.map (fun ast -> EC.unit ~elpi ~flags ast) in
      let units = units |> List.map (fun unit -> P.intern_unit (None,unit,flags)) in
      dbname,units,vs,scope) in
    clauses_to_add |> List.iter (fun (dbname,units,vs,scope) ->
      P.accumulate_to_db dbname units vs ~scope);
    relocate_assignment_to_runtime,
    if P.stage = Summary.Stage.Synterp then API.State.get Coq_elpi_builtins_synterp.SynterpAction.log state |> List.rev
    else API.State.get Coq_elpi_builtins_synterp.SynterpAction.read state

let current_program = Summary.ref ~name:"elpi-cur-program-name" None
let set_current_program n =
  current_program := Some n

let typecheck_program ?program () =
  match !current_program with
  | None -> ()
  | Some program ->
      let elpi = P.ensure_initialized () in
      get_and_compile program |> Option.iter (fun (program, _) ->
        let query_ast = P.parse_goal ~elpi (API.Ast.Loc.initial "(typecheck)") "true." in
        let query = EC.query program query_ast in
        let _ = API.Setup.trace !trace_options in
        run_static_check query)
  
let current_program () =
  match !current_program with
  | None -> CErrors.user_err Pp.(str "No current Elpi Program")
  | Some x -> x

let run_in_program ?(program = current_program ()) ?(st_setup=fun x -> x) (loc, query) =
  let elpi = P.ensure_initialized () in
  get_and_compile ~even_if_empty:true program |> Option.map (fun (program_ast, _) ->
    let query_ast = `Ast (st_setup, P.parse_goal ~elpi loc query) in
    run_and_print ~print:true ~static_check:true program program_ast query_ast)

  let accumulate_extra_deps ?(program=current_program()) ids =
    let elpi = P.ensure_initialized () in
    let s = ids |> List.map (fun id ->
      try ComExtraDeps.query_extra_dep id
      with
      | Not_found when P.stage = Summary.Stage.Interp -> CErrors.anomaly Pp.(str"wtf")
      | Not_found ->
        err Pp.(str"File " ++ Names.Id.print id ++
          str" is unknown; please add a directive like 'From .. Extra Dependency .. as " ++
          Names.Id.print id ++ str"'.")) in
    try
      let new_src_ast = List.map (fun fname ->
        File {
          fname;
          fast = P.unit_from_file ~elpi fname;
        }) s in
        P.accumulate program new_src_ast
    with Failure s ->  CErrors.user_err Pp.(str s)
  let accumulate_extra_deps ~atts:(only,ph) ?program ids = skip ~only ~ph (accumulate_extra_deps ?program) ids
    
  let accumulate_files ?(program=current_program()) s =
    let elpi = P.ensure_initialized () in
    try
      let new_src_ast = List.map (fun fname ->
        File {
          fname;
          fast = P.unit_from_file ~elpi fname;
        }) s in
        P.accumulate program new_src_ast
    with Failure s ->  CErrors.user_err Pp.(str s)
  let accumulate_files ~atts:(only,ph) ?program s = skip ~only ~ph (accumulate_files ?program) s
  
  let accumulate_string ?(program=current_program()) (loc,s) =
    let elpi = P.ensure_initialized () in
    let new_ast = P.unit_from_string ~elpi loc s in
    if P.db_exists program then
      P.accumulate_to_db program [new_ast] [] ~scope:Coq_elpi_utils.Regular
    else
      P.accumulate program [EmbeddedString { sloc = loc; sdata = s; sast = new_ast}]
  let accumulate_string ~atts:(only,ph) ?program loc = skip ~only ~ph (accumulate_string ?program) loc
  
  
  let accumulate_db ?(program=current_program()) name =
    let _ = P.ensure_initialized () in
    if P.db_exists name then P.accumulate program [Database name]
    else CErrors.user_err Pp.(str "Db " ++ pr_qualified_name name ++ str" not found")
  let accumulate_db ~atts:(only,ph) ?program name = skip ~only ~ph (accumulate_db ?program) name
  
  
  let accumulate_to_db db (loc,s) idl ~scope =
    let elpi = P.ensure_initialized () in
    let new_ast = P.unit_from_string ~elpi loc s in
    if P.db_exists db then P.accumulate_to_db db [new_ast] idl ~scope
    else CErrors.user_err Pp.(str "Db " ++ pr_qualified_name db ++ str" not found") 
  let accumulate_to_db ~atts:(only,ph) db loc idl ~scope = skip ~only ~ph (accumulate_to_db db loc ~scope) idl
  

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
      
  let print name args =
    let elpi = P.ensure_initialized () in
    get_and_compile name |> Option.iter (fun (program, _) ->
      let args, fname, fname_txt =
        let default_fname = String.concat "." name ^ ".html" in
        let default_fname_txt = String.concat "." name ^ ".txt" in
        let default_blacklist = [
          "elaborator.elpi";"reduction.elpi";
          "coq-builtin.elpi";"coq-lib.elpi";"coq-HOAS.elpi"
        ] in
        match args with
        | [] -> default_blacklist, default_fname, default_fname_txt
        | [x] -> default_blacklist, x ^ ".html", x ^ ".txt"
        | x :: xs -> xs, x ^ ".html", x ^ ".txt" in
      let args = List.map API.RawOpaqueData.of_string args in
      let query_ast = Interp.parse_goal ~elpi (API.Ast.Loc.initial "(print)") "true." in
      let query = EC.query program query_ast in
      let oc = open_out fname_txt in
      let fmt = Format.formatter_of_out_channel oc in
    EPP.program fmt query;
    Format.pp_print_flush fmt ();
    close_out oc;
    let loc = { API.Ast.Loc.
      source_name = "(Elpi Print)";
      source_start = 0;
      source_stop = 0;
      line = -1;
      line_starts_at = 0; } in
    let q ~depth state =
      let state, quotedP, _  = API.Quotation.quote_syntax_compiletime state query in
      assert(depth=0); (* else, we should lift the terms down here *)
      let q = ET.mkApp main_quotedc
        (EU.list_to_lp_list quotedP)
        [API.RawOpaqueData.of_string fname; EU.list_to_lp_list args] in
      state, (loc,q), [] in
    ignore @@ run_and_print ~print:false ~static_check:false ["Elpi";"Print"]
      (P.assemble_units ~elpi [P.printer ()]) (`Fun q))
  let print ~atts name args = skip ~ph:atts (print name) args
      

  let create_command ~atts:(raw_args) n =
    let raw_args = Option.default false raw_args in
    let _ = P.ensure_initialized () in
    P.declare_program n (Command { raw_args });
    P.init_program n (P.command_init());
    set_current_program (snd n)

  let create_tactic n =
    let _ = P.ensure_initialized () in
    P.declare_program n Tactic;
    if P.stage = Summary.Stage.Interp then P.init_program n (P.tactic_init ());
    set_current_program (snd n)

  let create_program ~atts:(raw_args) n ~init:(loc,s) =
    let raw_args = Option.default false raw_args in
    let elpi = P.ensure_initialized () in
    P.declare_program n (Program { raw_args });
    let unit = P.unit_from_string ~elpi loc s in
    let init = EmbeddedString { sloc = loc; sdata = s; sast = unit} in
    P.init_program n init;
    set_current_program (snd n)

  let create_db ~atts n ~init:(loc,s) =
    let do_init =
      match atts with
      | None -> same_phase Interp P.stage
      | Some phase -> same_phase phase P.stage in
    let elpi = P.ensure_initialized () in
    P.declare_db n;
    if do_init then
      let unit = P.unit_from_string ~elpi loc s in
      P.init_db n unit  

  let load_command = P.load_command
  let load_tactic = P.load_tactic
  let load_printer = P.load_printer
  let load_checker = P.load_checker

  let get_and_compile qn = get_and_compile ?even_if_empty:None qn

end

module type Common = sig
  val typecheck_program : ?program:qualified_name -> unit -> unit
  val get_and_compile :
    qualified_name -> (Elpi.API.Compile.program * bool) option
  val run : static_check:bool ->
    Elpi.API.Compile.program ->
     [ `Ast of (Elpi.API.State.t -> Elpi.API.State.t) * Elpi.API.Ast.query
     | `Fun of
         depth:int ->
         Elpi.API.State.t ->
         Elpi.API.State.t *
         (Elpi.API.Ast.Loc.t * Elpi.API.Data.term) *
         Elpi.API.Conversion.extra_goals ] ->
    unit Elpi.API.Execute.outcome  

  val accumulate_files       : atts:((Str.regexp list option * Str.regexp list option) * phase option) -> ?program:qualified_name -> string list -> unit
  val accumulate_extra_deps  : atts:((Str.regexp list option * Str.regexp list option) * phase option) -> ?program:qualified_name -> Names.Id.t list -> unit
  val accumulate_string      : atts:((Str.regexp list option * Str.regexp list option) * phase option) -> ?program:qualified_name -> Elpi.API.Ast.Loc.t * string -> unit
  val accumulate_db          : atts:((Str.regexp list option * Str.regexp list option) * phase option) -> ?program:qualified_name -> qualified_name -> unit
  val accumulate_to_db       : atts:((Str.regexp list option * Str.regexp list option) * phase option) -> qualified_name -> Elpi.API.Ast.Loc.t * string -> Names.Id.t list -> scope:Coq_elpi_utils.clause_scope -> unit
  
  val load_checker : string -> unit
  val load_printer : string -> unit
  val load_tactic : string -> unit
  val load_command : string -> unit

  val debug         : atts:phase option -> string list -> unit
  val trace         : atts:phase option -> int -> int -> string list -> string list -> unit
  val trace_browser : atts:phase option -> string list -> unit
  val bound_steps   : atts:phase option -> int -> unit
  val print         : atts:phase option -> qualified_name -> string list -> unit

  val create_program : atts:bool option -> program_name -> init:(Elpi.API.Ast.Loc.t * string) -> unit
  val create_command : atts:bool option -> program_name -> unit
  val create_tactic : program_name -> unit
  val create_db : atts:phase option -> program_name -> init:(Elpi.API.Ast.Loc.t * string) -> unit

end

module Synterp = struct
  include Compiler(Coq_elpi_programs.Synterp)

  let main_syterp args syndata =
    ET.mkApp API.RawData.Constants.orc
      (ET.mkApp main_synterpc (EU.list_to_lp_list args) [syndata])
      [ET.mkApp mainc (EU.list_to_lp_list args) []]
  
  let run_program loc name ~atts args =
    get_and_compile name |> Option.map (fun (program, raw_args) ->
      let loc = Coq_elpi_utils.of_coq_loc loc in
      let query ~depth state =
        let state, args, gls = EU.map_acc
          (Coq_elpi_arg_HOAS.in_elpi_cmd_synterp ~depth)
          state args in
        let state, ek = API.FlexibleData.Elpi.make ~name:"NewData" state in
        let data = ET.mkUnifVar ek ~args:[] state in
        let state, q = atts2impl loc Summary.Stage.Synterp ~depth state atts (main_syterp args data) in
        let state = API.State.set Coq_elpi_builtins_synterp.invocation_site_loc_synterp state loc in
        state, (loc, q), gls in
      try
        let relocate, synterplog = run_and_print ~print:false ~static_check:false name program (`Fun query) in
        relocate "NewData", synterplog
      with Coq_elpi_builtins_synterp.SynterpAction.Error x -> err x)

  let run_in_program ?program query =
    try run_in_program ?program query |> Option.map (fun (_,x) -> x)
    with Coq_elpi_builtins_synterp.SynterpAction.Error x -> err x
    
end

let document_builtins = document_builtins

module Interp = struct

  include Compiler(Coq_elpi_programs.Interp)

  let main_interp args syndata =
    ET.mkApp API.RawData.Constants.orc
     (ET.mkApp main_interpc (EU.list_to_lp_list args) [syndata])
     [ET.mkApp mainc (EU.list_to_lp_list args) []]
    
  let missing_synterp = let open Pp in
    fnl() ++
    strbrk "The command lacks code for the synterp phase. In order to add code to this phase use '#[synterp] Elpi Accumulate'. See also https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_command.html#parsing-and-execution"
 
 
  let run_program loc name ~atts ~syndata args =
    get_and_compile name |> Option.iter (fun (program, raw_args) ->
      let loc = Coq_elpi_utils.of_coq_loc loc in
      let env = Global.env () in
      let sigma = Evd.from_env env in
      let args = args
        |> List.map (Coq_elpi_arg_HOAS.Cmd.glob (Genintern.empty_glob_sign ~strict:true env))
        |> List.map (Coq_elpi_arg_HOAS.Cmd.interp (Ltac_plugin.Tacinterp.default_ist ()) env sigma)
      in
      let synterplog, synterm =
        match syndata with
        | None -> [], fun ~target:_ ~depth -> Stdlib.Result.Ok ET.mkDiscard
        | Some (relocate_term,log) -> log, relocate_term in
      let initial_synterp_state =
        match synterplog with
        | [] -> Vernacstate.Synterp.freeze ()
        | x :: _ -> Coq_elpi_builtins_synterp.SynterpAction.synterp_state_after x in
      let query ~depth state =
        let state, args, gls = EU.map_acc
          (Coq_elpi_arg_HOAS.in_elpi_cmd ~depth ~raw:raw_args Coq_elpi_HOAS.(mk_coq_context ~options:(default_options ()) state))
          state args in
        let synterm =
          match synterm ~target:state ~depth with
          | Stdlib.Result.Ok x -> x
          | Stdlib.Result.Error s -> err Pp.(str"Data returned by the synterp phase cannot be passed to the interp phase due to unknown symbol: " ++ str s) in
          
        let state, q = atts2impl loc Summary.Stage.Interp ~depth state atts (main_interp args synterm) in
        let state = API.State.set Coq_elpi_builtins.tactic_mode state false in
        let state = API.State.set Coq_elpi_builtins_synterp.invocation_site_loc state loc in
        let state = API.State.set Coq_elpi_builtins_synterp.SynterpAction.read state synterplog in
        state, (loc, q), gls in
      let final_synterp_state = Vernacstate.Synterp.freeze () in
      Vernacstate.Synterp.unfreeze initial_synterp_state;
      try begin
        try 
            let _, synterp_left = run_and_print ~print:false ~static_check:false name program (`Fun query) in
            match synterp_left with
            | [] -> Vernacstate.Synterp.unfreeze final_synterp_state
            | x :: _ ->
                err Pp.(strbrk"The execution phase did not consume all the parse time actions. Next in the queue is " ++ Coq_elpi_builtins_synterp.SynterpAction.pp x)
        with
        | Coq_elpi_builtins_synterp.SynterpAction.Error x when syndata = None ->
            err Pp.(x ++ missing_synterp)
        | Coq_elpi_builtins_synterp.SynterpAction.Error x ->
            err x
      end with e ->
        let e = Exninfo.capture e in
        Vernacstate.Synterp.unfreeze final_synterp_state;
        Exninfo.iraise e)
  
  let run_in_program ?program ~syndata query =
    let st_setup state =
      let syndata = Option.default [] syndata in
      API.State.set Coq_elpi_builtins_synterp.SynterpAction.read state syndata in
    try ignore @@ run_in_program ?program ~st_setup query
    with
    | Coq_elpi_builtins_synterp.SynterpAction.Error x when syndata = None -> err Pp.(x ++ missing_synterp)
    | Coq_elpi_builtins_synterp.SynterpAction.Error x -> err x

            
end

open Tacticals

let run_tactic_common loc ?(static_check=false) program ~main ?(atts=[]) () =
  let open Proofview in
  let open Notations in
  let open Interp in
  Unsafe.tclGETGOALS >>= fun gls ->
  let gls = CList.map Proofview.drop_state gls in
  Proofview.tclEVARMAP >>= fun sigma ->
  let query ~depth state = 
    let state, (loc, q), gls =
      Coq_elpi_HOAS.goals2query sigma gls loc ~main
        ~in_elpi_tac_arg:Coq_elpi_arg_HOAS.in_elpi_tac ~depth state in
    let state, qatts = atts2impl loc Summary.Stage.Interp ~depth state atts q in
    let state = API.State.set Coq_elpi_builtins.tactic_mode state true in
    let state = API.State.set Coq_elpi_builtins_synterp.invocation_site_loc state loc in
    state, (loc, qatts), gls
    in
  get_and_compile program |> Option.cata (fun (cprogram, _) ->
    match run ~static_check cprogram (`Fun query) with
    | API.Execute.Success solution -> Coq_elpi_HOAS.tclSOLUTION2EVD sigma solution
    | API.Execute.NoMoreSteps -> CErrors.user_err Pp.(str "elpi run out of steps")
    | API.Execute.Failure -> elpi_fails program
    | exception (Coq_elpi_utils.LtacFail (level, msg)) -> tclFAILn level msg)
  tclIDTAC

let run_tactic loc program ~atts _ist args =
  let loc = Coq_elpi_utils.of_coq_loc loc in
  run_tactic_common loc program ~main:(Coq_elpi_HOAS.Solve args) ~atts ()

let run_in_tactic ?(program = Interp.current_program ()) (loc,query) _ist =
  run_tactic_common loc ~static_check:true program ~main:(Coq_elpi_HOAS.Custom query) ()

let loc_merge l1 l2 =
  try Loc.merge l1 l2
  with Failure _ -> l1

let cache_program (nature,p,q) =
  let p_str = String.concat "." q in
  match nature with
  | Command _ ->
    let command = Vernacexpr.{
      ext_plugin = "coq-elpi.elpi";
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
              (Genarg.get_arg_tag Coq_elpi_arg_syntax.wit_elpi_loc),
            Vernacextend.TyTerminal
              (p_str,
               Vernacextend.TyNonTerminal
                 (Extend.TUlist0
                    (Extend.TUentry (Genarg.get_arg_tag Coq_elpi_arg_syntax.wit_elpi_cmd_arg))
                 ,Vernacextend.TyNonTerminal
                     (Extend.TUentry (Genarg.get_arg_tag Coq_elpi_arg_syntax.wit_elpi_loc),
                      Vernacextend.TyNil)))))

        (fun loc0 args loc1 ?loc ~atts () ->
          let loc = Option.default (loc_merge loc0 loc1) loc in
          let syndata = Synterp.run_program loc p ~atts args in
          Vernactypes.vtdefault (fun () ->
             Interp.run_program loc p ~atts ~syndata args))
    in
    Egramml.extend_vernac_command_grammar ~undoable:true ext

  | Tactic ->
    Coq_elpi_builtins.cache_tac_abbrev ~code:p ~name:q
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
  let nature = Coq_elpi_programs.Synterp.get_nature p in
  Lib.add_leaf (in_exported_program (nature,p,q))

