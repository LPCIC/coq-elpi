(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
module EC = API.Compile
module EPP = API.Pp
module EU = API.Utils
module ET = API.RawData

open Coq_elpi_utils
module Programs = Coq_elpi_programs

(* ******************** Vernacular commands ******************************* *)

open Programs

let load_command = load_command
let load_tactic = load_tactic
let load_printer = load_printer
let load_checker = load_checker
let document_builtins = document_builtins

let create_command ?(raw_args=false) n =
  let _ = ensure_initialized () in
  create_program n (Command { raw_args }) (command_init());
  set_current_program (snd n)

let create_tactic n =
  let _ = ensure_initialized () in
  create_program n Tactic (tactic_init ());
  set_current_program (snd n)

let create_program ?(raw_args=false) n ~init:(loc,s) =
  let elpi = ensure_initialized () in
  let unit = unit_from_string ~elpi loc s in
  let init = EmbeddedString { sloc = loc; sdata = s; sast = unit} in
  create_program n (Program { raw_args }) init;
  set_current_program (snd n)

let create_db n ~init:(loc,s) =
  let elpi = ensure_initialized () in
  let unit = unit_from_string ~elpi loc s in
  create_db n unit

let default_max_step = max_int

let trace_options = Summary.ref ~name:"elpi-trace" []
let max_steps = Summary.ref ~name:"elpi-steps" default_max_step

let debug vl = debug_vars := List.fold_right EC.StrSet.add vl EC.StrSet.empty

let bound_steps n =
  if n <= 0 then max_steps := default_max_step else max_steps := n

(* Units are marshalable, but programs are not *)

let compiler_cache_code = Summary.ref ~local:true
  ~name:"elpi-compiler-cache-code"
  Int.Map.empty
let compiler_cache_chunk = Summary.ref ~local:true
  ~name:"elpi-compiler-cache-chunk"
  Int.Map.empty

let programs_tip = Summary.ref ~local:true
  ~name:"elpi-compiler-cache-gc"
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

let get_and_compile name =
  let src = code name in
  let prog =
    let rec compile_code src =
      let h = Code.hash src in
      try
        lookup_code 0 h src
      with Not_found ->
        match src with
        | Code.Base { base = (k,u) } ->
            let elpi = ensure_initialized () in
            let prog = assemble_units ~elpi [u] in
            cache_code 0 h prog src
        | Code.Snoc { prev; source } ->
            let base = compile_code prev in
            let prog = extend_w_units ~base [snd source] in
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
          let prog = extend_w_units ~base [u] in
          cache_chunk bh h prog src
      | Chunk.Snoc { prev; source_rev } ->
          let base = compile_chunk bh base prev in
          let prog = extend_w_units ~base (List.rev_map snd source_rev) in
          recache_chunk bh (Chunk.hash prev) h prog src
    in
    let prog = compile_code src in
    let new_hash = Code.hash src in
    let old_hash = try SLMap.find name !programs_tip with Not_found -> 0 in
    programs_tip := SLMap.add name new_hash !programs_tip;
    recache_code 0 old_hash new_hash prog src in
  let raw_args =
    match get_nature name with
    | Command { raw_args } -> raw_args
    | Program { raw_args } -> raw_args
    | Tactic -> true in
  prog, raw_args

let run_static_check query =
  let checker = 
    let elpi = ensure_initialized () in
    assemble_units ~elpi (checker()) in
  (* We turn a failure into a proper error in etc/coq-elpi_typechecker.elpi *)
  ignore (EC.static_check ~checker query)

let run ~static_check program query =
  let t1 = Unix.gettimeofday () in
  let query =
    match query with
    | `Ast query_ast -> EC.query program query_ast
    | `Fun query_builder -> API.RawQuery.compile program query_builder in
  let t2 = Unix.gettimeofday () in
  let _ = API.Setup.trace [] in
  if static_check then run_static_check query;
  let t3 = Unix.gettimeofday () in
  let leftovers = API.Setup.trace !trace_options in
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
    "The elpi"; kind; name ; "failed without giving a specific error message.";
    "Please report this inconvenience to the authors of the program."
  ]))
   
let run_and_print ~print ~static_check program_name program_ast query_ast : unit =
  let open API.Data in let open Coq_elpi_utils in
  match run ~static_check program_ast query_ast
  with
  | API.Execute.Failure -> elpi_fails program_name
  | API.Execute.NoMoreSteps ->
      CErrors.user_err Pp.(str "elpi run out of steps ("++int !max_steps++str")")
  | API.Execute.Success {
     assignments ; constraints; state; pp_ctx
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
      let sigma = Coq_elpi_HOAS.get_sigma state in
      let ccst = Evd.evar_universe_context sigma in
      if not (UState.is_empty ccst) then
        Feedback.msg_notice Pp.(str"Universe constraints:" ++ spc() ++
          Termops.pr_evar_universe_context ccst)
    end;
    (* We add clauses declared via coq.elpi.accumulate *)
    let clauses_to_add =
      API.State.get Coq_elpi_builtins.clauses_for_later
        state in
    let elpi = ensure_initialized () in
    let flags = cc_flags() in
    let clauses_to_add = clauses_to_add |> group_clauses |>
      List.map (fun (dbname,asts,vs,scope) ->
      let units = asts |> List.map (fun ast -> EC.unit ~elpi ~flags ast) in
      let units = units |> List.map (fun unit -> intern_unit (None,unit,flags)) in
      dbname,units,vs,scope) in
    clauses_to_add |> List.iter (fun (dbname,units,vs,scope) ->
      accumulate_to_db dbname units vs ~scope)
;;

let run_in_program ?(program = current_program ()) (loc, query) =
  let elpi = ensure_initialized () in
  let program_ast, _ = get_and_compile program in
  let query_ast = `Ast (parse_goal ~elpi loc query) in
  run_and_print ~print:true ~static_check:true program program_ast query_ast
;;

let typecheck_program ?(program = current_program ()) () =
  let elpi = ensure_initialized () in
  let program, _ = get_and_compile program in
  let query_ast = parse_goal ~elpi (API.Ast.Loc.initial "(typecheck)") "true." in
  let query = EC.query program query_ast in
  let _ = API.Setup.trace !trace_options in
  run_static_check query
;;

let mainc = ET.Constants.declare_global_symbol "main"
let attributesc = ET.Constants.declare_global_symbol "attributes"

let atts2impl loc ~depth state atts q =
  let open Coq_elpi_builtins in
  let rec convert_att_r = function
    | (name,Attributes.VernacFlagEmpty) -> name, AttributeEmpty
    | (name,Attributes.VernacFlagList l) -> name, AttributeList (convert_atts l)
    | (name,Attributes.VernacFlagLeaf v) -> name, AttributeLeaf (convert_att_value v)
  and convert_att att = convert_att_r att.CAst.v
  and convert_atts l = List.map convert_att l
  and convert_att_value = function
    Attributes.FlagIdent s | Attributes.FlagString s -> AttributeString s
  in
  let atts = ("elpi.loc", AttributeLeaf (AttributeLoc loc)) :: convert_atts atts in
  let atts =
    match Sys.getenv_opt "COQ_ELPI_ATTRIBUTES" with
    | None -> atts
    | Some txt ->
        match Pcoq.parse_string (Pvernac.main_entry None) (Printf.sprintf "#[%s] Qed." txt) |> Option.map (fun x -> x.CAst.v) with
        | None -> atts
        | Some { Vernacexpr.attrs ; _ } -> List.map (fun {CAst.v=(name,v)} -> convert_att_r ("elpi."^name,v)) attrs @ atts
        | exception Gramlib.Stream.Error msg ->
            CErrors.user_err Pp.(str"Environment variable COQ_ELPI_ATTRIBUTES contains ill formed value:" ++ spc () ++ str txt ++ cut () ++ str msg) in
  let state, atts, _ = EU.map_acc (Coq_elpi_builtins.attribute.API.Conversion.embed ~depth) state atts in
  let atts = ET.mkApp attributesc (EU.list_to_lp_list atts) [] in
  state, ET.mkApp ET.Constants.implc atts [q] 
;;
let run_program loc name ~atts args =
  let program, raw_args = get_and_compile name in
  let loc = Coq_elpi_utils.of_coq_loc loc in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let args = args
    |> List.map (Coq_elpi_arg_HOAS.Cmd.glob (Genintern.empty_glob_sign ~strict:true env))
    |> List.map (Coq_elpi_arg_HOAS.Cmd.interp (Ltac_plugin.Tacinterp.default_ist ()) env sigma)
  in
  let query ~depth state =
    let state, args, gls = EU.map_acc
      (Coq_elpi_arg_HOAS.in_elpi_cmd ~depth ~raw:raw_args Coq_elpi_HOAS.(mk_coq_context ~options:(default_options ()) state))
      state args in
    let state, q = atts2impl loc ~depth state atts (ET.mkApp mainc (EU.list_to_lp_list args) []) in
    let state = API.State.set Coq_elpi_builtins.tactic_mode state false in
    let state = API.State.set Coq_elpi_builtins.invocation_site_loc state loc in
    state, (loc, q), gls in

  run_and_print ~print:false ~static_check:false name program (`Fun query)
;;

let mk_trace_opts start stop preds =
  [ "-trace-on"
  ; "-trace-at"; "run"; string_of_int start; string_of_int stop
  ; "-trace-only"; "\\(run\\|select\\|user:\\)"
  ; "-trace-tty-maxbox"; "30"
  ] @ List.(flatten (map (fun x -> ["-trace-only-pred"; x]) preds))

let trace start stop preds opts =
  if start = 0 && stop = 0 then trace_options := []
  else trace_options := mk_trace_opts start stop preds @ opts

let trace_browser _opts =
  trace_options :=
    [ "-trace-on"; "json"; "/tmp/traced.tmp.json"
    ; "-trace-at"; "run"; "0"; string_of_int max_int
    ; "-trace-only"; "user"
    ];
  Feedback.msg_notice
    Pp.(strbrk "Now click \"Start watching\" in the Elpi Trace Browser panel and then execute the Command/Tactic/Query you want to trace. Also try \"F1 Elpi\".")

let main_quotedc = ET.Constants.declare_global_symbol "main-quoted"

let print name args =
  let elpi = ensure_initialized () in
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
  let program, _ = get_and_compile name in
  let query_ast = parse_goal ~elpi (API.Ast.Loc.initial "(print)") "true." in
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
  run_and_print ~print:false ~static_check:false ["Elpi";"Print"]
    (assemble_units ~elpi [printer ()]) (`Fun q)
;;

open Tacticals

let run_tactic_common loc ?(static_check=false) program ~main ?(atts=[]) () =
  let open Proofview in
  let open Notations in
  Unsafe.tclGETGOALS >>= fun gls ->
  let gls = CList.map Proofview.drop_state gls in
  Proofview.tclEVARMAP >>= fun sigma ->
  let query ~depth state = 
    let state, (loc, q), gls =
      Coq_elpi_HOAS.goals2query sigma gls loc ~main
        ~in_elpi_tac_arg:Coq_elpi_arg_HOAS.in_elpi_tac ~depth state in
    let state, qatts = atts2impl loc ~depth state atts q in
    let state = API.State.set Coq_elpi_builtins.tactic_mode state true in
    let state = API.State.set Coq_elpi_builtins.invocation_site_loc state loc in
    state, (loc, qatts), gls
    in
  let cprogram, _ = get_and_compile program in
  match run ~static_check cprogram (`Fun query) with
  | API.Execute.Success solution -> Coq_elpi_HOAS.tclSOLUTION2EVD sigma solution
  | API.Execute.NoMoreSteps -> CErrors.user_err Pp.(str "elpi run out of steps")
  | API.Execute.Failure -> elpi_fails program
  | exception (Coq_elpi_utils.LtacFail (level, msg)) -> tclFAILn level msg

let run_tactic loc program ~atts _ist args =
  let loc = Coq_elpi_utils.of_coq_loc loc in
  run_tactic_common loc program ~main:(Coq_elpi_HOAS.Solve args) ~atts ()

let run_in_tactic ?(program = current_program ()) (loc,query) _ist =
  run_tactic_common loc ~static_check:true program ~main:(Coq_elpi_HOAS.Custom query) ()

let accumulate_extra_deps ?(program=current_program()) ids =
  let elpi = ensure_initialized () in
  let s = ids |> List.map (fun id ->
    try ComExtraDeps.query_extra_dep id
    with Not_found ->
      err Pp.(str"File " ++ Names.Id.print id ++
        str" is unknown; please add a directive like 'From .. Extra Dependency .. as " ++
        Names.Id.print id ++ str"'.")) in
  try
    let new_src_ast = List.map (fun fname ->
      File {
        fname;
        fast = unit_from_file ~elpi fname;
      }) s in
    accumulate program new_src_ast
  with Failure s ->  CErrors.user_err Pp.(str s)
  ;;
  
let accumulate_files ?(program=current_program()) s =
  let elpi = ensure_initialized () in
  try
    let new_src_ast = List.map (fun fname ->
      File {
        fname;
        fast = unit_from_file ~elpi fname;
      }) s in
    accumulate program new_src_ast
  with Failure s ->  CErrors.user_err Pp.(str s)
 ;;

let accumulate_string ?(program=current_program()) (loc,s) =
  let elpi = ensure_initialized () in
  let new_ast = unit_from_string ~elpi loc s in
  if db_exists program then
    accumulate_to_db program [new_ast] [] ~scope:Coq_elpi_utils.Regular
  else
    accumulate program [EmbeddedString { sloc = loc; sdata = s; sast = new_ast}]
;;

let accumulate_db ?(program=current_program()) name =
  let _ = ensure_initialized () in
  if db_exists name then accumulate program [Database name]
  else CErrors.user_err
    Pp.(str "Db " ++ pr_qualified_name name ++ str" not found") 

let accumulate_to_db db (loc,s) =
  let elpi = ensure_initialized () in
  let new_ast = unit_from_string ~elpi loc s in
  if db_exists db then accumulate_to_db db [new_ast]
  else CErrors.user_err
    Pp.(str "Db " ++ pr_qualified_name db ++ str" not found") 

let loc_merge l1 l2 =
  try Loc.merge l1 l2
  with Failure _ -> l1

let cache_program (nature,p,p_str) =
  match nature with
  | Command _ ->
    let ext =
      Vernacextend.declare_dynamic_vernac_extend
        ~command:("Elpi"^p_str)
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

        (fun loc0 args loc1 ?loc ~atts () -> Vernacextend.vtdefault (fun () ->
             run_program (Option.default (loc_merge loc0 loc1) loc) p ~atts args))
    in
    Egramml.extend_vernac_command_grammar ~undoable:true ext

  | Tactic ->
    Coq_elpi_builtins.cache_tac_abbrev p
  | Program _ ->
    CErrors.user_err Pp.(str "elpi: Only commands and tactics can be exported")

let subst_program = function
  | _, (Command _, _, _) -> CErrors.user_err Pp.(str"elpi: No functors yet")
  | _, (Tactic,_,_ as x) -> x
  | _, (Program _,_,_) -> assert false

let in_exported_program : nature * qualified_name * string -> Libobject.obj =
  let open Libobject in
  declare_object @@ global_object_nodischarge "ELPI-EXPORTED"
    ~cache:cache_program
    ~subst:(Some subst_program)

let export_command p =
  let p_str = String.concat "." p in
  let nature = get_nature p in
  Lib.add_leaf (in_exported_program (nature,p,p_str))

let skip ~atts:(skip,only) f x =
  let m rex = Str.string_match rex Coq_config.version 0 in
  let exec =
    match skip, only with
    | None, None -> true
    | Some skip, None -> not (List.exists m skip)
    | None, Some keep -> List.exists m keep
    | Some _, Some _ -> CErrors.user_err Pp.(str "Attributes #[skip] and #[only] cannot be used at the same time")
  in
    if exec then f x else ()


