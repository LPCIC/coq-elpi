(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
module EC = API.Compile
module EP = API.Parse
module EPP = API.Pp
module EU = API.Utils
module ET = API.RawData

let debug_vars = Summary.ref ~name:"elpi-debug" EC.StrSet.empty

let cc_flags () =
  { EC.default_flags with EC.defined_variables = !debug_vars }

let unit_from_file ~elpi x =
  try EC.unit ~elpi ~flags:(cc_flags ()) (EP.program ~elpi ~print_accumulated_files:false x)
  with
  | EP.ParseError(loc, msg) ->
    let loc = Coq_elpi_utils.to_coq_loc loc in
    CErrors.user_err ~loc ~hdr:"elpi" (Pp.str msg)
  | EC.CompileError(oloc, msg) ->
    let loc = Option.map Coq_elpi_utils.to_coq_loc oloc in
    CErrors.user_err ?loc ~hdr:"elpi" (Pp.str msg)

let unit_from_string ~elpi loc x =
  let x = Stream.of_string x in
  try EC.unit ~elpi ~flags:(cc_flags ()) (EP.program_from_stream ~elpi ~print_accumulated_files:false loc x)
  with
  | EP.ParseError(loc, msg) ->
    let loc = Coq_elpi_utils.to_coq_loc loc in
    CErrors.user_err ~loc ~hdr:"elpi" (Pp.str msg)
  | EC.CompileError(oloc, msg) ->
    let loc = Option.map Coq_elpi_utils.to_coq_loc oloc in
    CErrors.user_err ?loc ~hdr:"elpi" (Pp.str msg)

let parse_goal loc x =
  try EP.goal loc x
  with EP.ParseError(loc, msg) ->
    let loc = Coq_elpi_utils.to_coq_loc loc in
    CErrors.user_err ~loc ~hdr:"elpi" (Pp.str msg)


type qualified_name = string list [@@deriving ord]
let pr_qualified_name = Pp.prlist_with_sep (fun () -> Pp.str".") Pp.str
let show_qualified_name = String.concat "."
let _pp_qualified_name fmt l = Format.fprintf fmt "%s" (String.concat "." l)

type expr_record_decl = {
  name : qualified_name;
  arity : Constrexpr.local_binder_expr list * Glob_term.glob_sort option;
  constructor : Names.Id.t option;
  fields : Vernacexpr.local_decl_expr Vernacexpr.with_instance Vernacexpr.with_priority Vernacexpr.with_notation list
}
let pr_expr_record_decl _ _ { name; arity; constructor; fields } = Pp.str "TODO: pr_expr_record_decl"

type ('a,'b) arg =
  | Int of int
  | String of string
  | Qualid of qualified_name
  | DashQualid of qualified_name
  | Term of 'a
  | RecordDecl of 'b

let pr_arg f g = function
  | Int n -> Pp.int n
  | String s -> Pp.qstring s
  | Qualid s -> pr_qualified_name s
  | DashQualid s -> Pp.(str"- " ++ pr_qualified_name s)
  | Term s -> f s
  | RecordDecl s -> g s

let intern_record_decl glob_sign { name; arity = (spine,sort); constructor; fields } =
  let sort = match sort with
    | Some x -> Constrexpr.CSort x
    | None -> Constrexpr.CSort (Glob_term.GType []) in
  let arity =
    Ltac_plugin.Tacintern.intern_constr glob_sign @@ Constrexpr_ops.mkProdCN spine @@ CAst.make sort in
  let push_name x = function
    | { CAst.v = Names.Name.Name id } ->
        let decl = Context.Named.Declaration.LocalAssum (Context.make_annot id Sorts.Relevant, Constr.mkProp) in
        { x with Genintern.genv = Environ.push_named decl x.Genintern.genv }
    | _ -> x in
  let glob_sign_params =
    List.fold_left (fun gs -> function
      | Constrexpr.CLocalAssum (l,_,_) -> List.fold_left push_name gs l
      | Constrexpr.CLocalDef (n,_,_) -> push_name gs n
      | Constrexpr.CLocalPattern _ -> Coq_elpi_utils.nYI "CLocalPattern") glob_sign spine
    in
  let _, fields =
    List.fold_left (fun (gs,acc) -> function
    | (((inst,Vernacexpr.AssumExpr ({ CAst.v = name } as fn,x)),pr),nots) ->
        if nots <> [] then Coq_elpi_utils.nYI "notation in record fields";
        if pr <> None then Coq_elpi_utils.nYI "priority in record fields";
        if inst = Some false then Coq_elpi_utils.nYI "instance :>> flag in record fields";
        push_name gs fn, (name, inst <> None, Ltac_plugin.Tacintern.intern_constr gs x) :: acc
    | (((_,Vernacexpr.DefExpr _),_),_) -> Coq_elpi_utils.nYI "DefExpr")
        (glob_sign_params,[]) fields in
  { Coq_elpi_goal_HOAS.name = List.map Names.Id.of_string name; arity; constructor; fields = List.rev fields }

let subst_record_decl s { Coq_elpi_goal_HOAS.name; arity; constructor; fields } =
  let arity = Ltac_plugin.Tacsubst.subst_glob_constr_and_expr s arity in
  let fields = List.map (fun (id,coe,t) -> id, coe, Ltac_plugin.Tacsubst.subst_glob_constr_and_expr s t) fields in
  { Coq_elpi_goal_HOAS.name; arity; constructor; fields }

let glob_arg glob_sign = function
  | Qualid _ as x -> x
  | DashQualid _ as x -> x
  | Int _ as x -> x
  | String _ as x -> x
  | Term t -> Term (Ltac_plugin.Tacintern.intern_constr glob_sign t)
  | RecordDecl t -> RecordDecl (intern_record_decl glob_sign t)

let interp_arg ist evd = function
  | Qualid _ as x -> evd.Evd.sigma, x
  | DashQualid _ as x -> evd.Evd.sigma, x
  | Int _ as x -> evd.Evd.sigma, x
  | String _ as x -> evd.Evd.sigma, x
  | Term t -> evd.Evd.sigma, (Term(ist,t))
  | RecordDecl t -> evd.Evd.sigma, (RecordDecl(ist,t))

type program_name = Loc.t * qualified_name

module SLMap = Map.Make(struct
  type t = qualified_name
  let compare = compare_qualified_name
end)

(* ******************** Vernacular commands ******************************* *)

module Programs : sig
open API
type src =
  | File of src_file
  | EmbeddedString of src_string
  | Database of qualified_name
and src_file = {
  fname : string;
  fast : Compile.compilation_unit
}
and src_string = {
  sloc : Ast.Loc.t;
  sdata : string;
  sast : Compile.compilation_unit
}

  val get : qualified_name -> Compile.compilation_unit list

  val create_program : program_name -> src -> unit
  val create_db : program_name -> src -> unit

  val set_current_program : qualified_name -> unit
  val current_program : unit -> qualified_name
  val accumulate : qualified_name -> src list -> unit
  val accumulate_to_db : qualified_name -> Compile.compilation_unit list -> unit

  val load_checker : string -> unit
  val load_printer : string -> unit
  val load_command : string -> unit
  val load_tactic : string -> unit
  val document_builtins : unit -> unit

  val ensure_initialized : unit -> Setup.elpi

  val db_exists : qualified_name -> bool

  val checker : unit -> Compile.compilation_unit list
  val printer : unit -> Compile.compilation_unit

  val tactic_init : unit -> src
  val command_init : unit -> src

end = struct

type src =
  | File of src_file
  | EmbeddedString of src_string
  | Database of qualified_name
and src_file = {
  fname : string;
  fast : EC.compilation_unit [@compare fun _ _ -> 0 ] [@opaque]
}
and src_string = {
  sloc : API.Ast.Loc.t;
  sdata : string;
  sast : EC.compilation_unit [@compare fun _ _ -> 0] [@opaque]
}
[@@deriving ord]

module SrcSet = Set.Make(struct type t = src let compare = compare_src end)

let current_program = Summary.ref ~name:"elpi-cur-program-name" None

let program_src = Summary.ref ~name:"elpi-programs" SLMap.empty
let program_exists name = SLMap.mem name !program_src

let db_name_src = Summary.ref ~name:"elpi-db" SLMap.empty
let db_exists name = SLMap.mem name !db_name_src

let ast_of_src = function
  | File { fast = a } -> [a]
  | EmbeddedString { sast = a } -> [a]
  | Database name ->
     try List.(flatten (map snd (SLMap.find name !db_name_src)))
     with Not_found ->
       CErrors.user_err Pp.(str "Unknown Db " ++ str (show_qualified_name name))

let get_paths () =
  let build_dir = Coq_elpi_config.elpi_dir in
  let installed_dirs =
    let valid_dir d = try Sys.is_directory d with Sys_error _ -> false in
    (Envars.coqlib () ^ "/user-contrib") :: Envars.coqpath
    |> List.map (fun p -> p ^ "/elpi/")
    |> ((@) [".";".."]) (* Hem, this sucks *)
    |> List.filter valid_dir
  in
  "." :: build_dir :: installed_dirs

(* Setup called *)
let elpi = Pervasives.ref None

let elpi_builtins =
  API.BuiltIn.declare
    ~file_name:"elpi-builtin.elpi"
    Elpi.Builtin.(core_builtins @
    elpi_builtins @ elpi_nonlogical_builtins @
    elpi_stdlib @ elpi_map @ elpi_set @
    io_builtins)

let coq_builtins =
  API.BuiltIn.declare
    ~file_name:"coq-builtin.elpi"
    Coq_elpi_builtins.coq_builtins

let init () =
  let e, _ = API.Setup.init ~builtins:[coq_builtins;elpi_builtins] ~basedir:"."
    List.(flatten (map (fun x -> ["-I";x]) (get_paths ()))) in
  elpi := Some e;
  e
;;

let ensure_initialized =
  let init = lazy (init ()) in
  fun () -> Lazy.force init
;;

let document_builtins () =
  API.BuiltIn.document_file coq_builtins;
  API.BuiltIn.document_file ~header:"% Generated file, do not edit" elpi_builtins

(* We load pervasives and coq-lib once and forall at the beginning *)
let get ?(fail_if_not_exists=false) p =
  let _elpi = ensure_initialized () in
  try SLMap.find p !program_src
  with Not_found ->
    if fail_if_not_exists then
      CErrors.user_err
        Pp.(str "No Elpi Program named " ++ pr_qualified_name p)
    else
      []

let append_to_prog name l =
  let prog = get name in
  let rec aux seen = function
    | [] -> []
    | x :: xs when SrcSet.mem x seen -> aux seen xs
    | x :: xs -> x :: aux (SrcSet.add x seen) xs in
  aux SrcSet.empty (prog @ l)

let in_program : qualified_name * src list -> Libobject.obj =
  Libobject.declare_object @@ Libobject.global_object_nodischarge "ELPI"
    ~cache:(fun (_,(name,src_ast)) ->
      program_src :=
        SLMap.add name (append_to_prog name src_ast) !program_src)
    ~subst:(Some (fun _ -> CErrors.user_err Pp.(str"elpi: No functors yet")))

let add_to_program name v =
  let obj = in_program (name, v) in
  Lib.add_anonymous_leaf obj
;;


let append_to_db name (uuid,data as l) =
  let db = try SLMap.find name !db_name_src with Not_found -> [] in
  let rec aux seen = function
    | [] -> []
    | (u,_) :: xs when List.mem u seen -> aux seen xs
    | (u,_ as x) :: xs -> x :: aux (u :: seen) xs in
  aux [] (db @ [l])

let in_db : qualified_name * EC.compilation_unit list -> Libobject.obj =
  Libobject.declare_object @@ Libobject.global_object_nodischarge "ELPI-DB"
    ~cache:(fun (uuid,(name,p)) ->
       db_name_src :=
         SLMap.add name (append_to_db name (uuid,p)) !db_name_src)
    ~subst:(Some (fun _ -> CErrors.user_err Pp.(str"elpi: No functors yet")))

let add_to_db name l =
  Lib.add_anonymous_leaf (in_db (name,l))

let lp_command_ast = Summary.ref ~name:"elpi-lp-command" None
let in_lp_command_src : src -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI-LP-COMMAND") with
    Libobject.load_function = (fun _ (_,x) -> lp_command_ast := Some x);
}
let load_command s =
  let elpi = ensure_initialized () in
  let ast = File {
    fname = s;
    fast = unit_from_file ~elpi [s]
  } in
  lp_command_ast := Some ast;
  Lib.add_anonymous_leaf (in_lp_command_src ast)
let command_init () =
  match !lp_command_ast with
  | None -> CErrors.user_err Pp.(str "Elpi CommandTemplate was not called")
  | Some ast -> ast

let lp_tactic_ast = Summary.ref ~name:"elpi-lp-tactic" None
let in_lp_tactic_ast : src -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI-LP-TACTIC") with
    Libobject.load_function = (fun _ (_,x) -> lp_tactic_ast := Some x);
}
let load_tactic s =
  let elpi = ensure_initialized () in
  let ast = File {
    fname = s;
    fast = unit_from_file ~elpi [s]
  } in
  lp_tactic_ast := Some ast;
  Lib.add_anonymous_leaf (in_lp_tactic_ast ast)
let tactic_init () =
  match !lp_tactic_ast with
  | None -> CErrors.user_err Pp.(str "Elpi TacticTemplate was not called")
  | Some ast -> ast

let create_program (loc,qualid) init =
  if program_exists qualid || db_exists qualid then
    CErrors.user_err Pp.(str "Program/Tactic/Db " ++ pr_qualified_name qualid ++ str " already exists")
  else
    add_to_program qualid [init]

let create_db (loc,qualid) init =
  if program_exists qualid || db_exists qualid then
    CErrors.user_err Pp.(str "Program/Tactic/Db " ++ pr_qualified_name qualid ++ str " already exists")
  else
    add_to_db qualid (ast_of_src init)
;;

let set_current_program n =
  let _ = ensure_initialized () in
  current_program := Some n

let current_program () =
  match !current_program with
  | None -> CErrors.user_err Pp.(str "No current Elpi Program")
  | Some x -> x

let get x =
  List.(flatten (map ast_of_src (get ~fail_if_not_exists:true x)))

let lp_checker_ast = Summary.ref ~name:"elpi-lp-checker" None
let in_lp_checker_ast : EC.compilation_unit list -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI-LP-CHECKER") with
    Libobject.load_function = (fun _ (_,x) -> lp_checker_ast := Some x);
}
let load_checker s =
  let elpi = ensure_initialized () in
  let basic_checker = unit_from_string ~elpi (Elpi.API.Ast.Loc.initial "(elpi-checker)") Elpi.Builtin_checker.code in
  let coq_checker = unit_from_file ~elpi [s] in
  let p = [basic_checker;coq_checker] in
  Lib.add_anonymous_leaf (in_lp_checker_ast p)
let checker () =
  match !lp_checker_ast with
  | None -> CErrors.user_err Pp.(str "Elpi Checker was not called")
  | Some ast -> ast

let lp_printer_ast = Summary.ref ~name:"elpi-lp-printer" None
let in_lp_printer_ast : EC.compilation_unit -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI-LP-PRINTER") with
    Libobject.load_function = (fun _ (_,x) -> lp_printer_ast := Some x);
}
let load_printer s =
  let elpi = ensure_initialized () in
  let ast = unit_from_file ~elpi [s] in
  lp_printer_ast := Some ast;
  Lib.add_anonymous_leaf (in_lp_printer_ast ast)
let printer () =
  match !lp_printer_ast with
  | None -> CErrors.user_err Pp.(str "Elpi Printer was not called")
  | Some ast -> ast

let accumulate p v =
  if not (program_exists p) then
    CErrors.user_err Pp.(str "No Elpi Program named " ++ pr_qualified_name p);
  add_to_program p v

let accumulate_to_db p v =
  if not (db_exists p) then
    CErrors.user_err Pp.(str "No Elpi Db " ++ pr_qualified_name p);
  add_to_db p v

end

let () = Coq_elpi_builtins.set_accumulate_to_db (Programs.ensure_initialized, (fun n x -> Programs.accumulate_to_db n [x]))
open Programs

let load_command = load_command
let load_tactic = load_tactic
let load_printer = load_printer
let load_checker = load_checker
let document_builtins = document_builtins

let create_command n =
  let _ = ensure_initialized () in
  create_program n (command_init());
  set_current_program (snd n)

let create_tactic n =
  let _ = ensure_initialized () in
  create_program n (tactic_init ());
  set_current_program (snd n)

let create_program n ~init:(loc,s) =
  let elpi = ensure_initialized () in
  let unit = unit_from_string ~elpi loc s in
  let init = EmbeddedString { sloc = loc; sdata = s; sast = unit} in
  create_program n init;
  set_current_program (snd n)

let create_db n ~init:(loc,s) =
  let elpi = ensure_initialized () in
  let unit = unit_from_string ~elpi loc s in
  let init = EmbeddedString { sloc = loc; sdata = s; sast = unit} in
  create_db n init

let run_static_check query =
  let elpi = ensure_initialized () in
  (* We turn a failure into a proper error in etc/coq-elpi_typechecker.elpi *)
  let checker = EC.assemble ~elpi (checker ()) in
  ignore (EC.static_check ~checker query)

let default_max_step = max_int

let trace_options = Summary.ref ~name:"elpi-trace" []
let max_steps = Summary.ref ~name:"elpi-steps" default_max_step

let debug vl = debug_vars := List.fold_right EC.StrSet.add vl EC.StrSet.empty 

let bound_steps n =
  if n <= 0 then max_steps := default_max_step else max_steps := n


let run ~tactic_mode ~static_check program_ast query =
  let elpi = ensure_initialized () in
  let program = EC.assemble ~elpi program_ast in
  let query =
    match query with
    | `Ast query_ast -> EC.query program query_ast
    | `Fun query_builder -> API.RawQuery.compile program query_builder in
  API.Setup.trace [];
  if static_check then run_static_check query;
  API.Setup.trace !trace_options;
  Coq_elpi_builtins.tactic_mode := tactic_mode;
  API.Execute.once ~max_steps:!max_steps (EC.optimize query)
;;

let run_and_print ~tactic_mode ~print ~static_check program_ast query_ast =
  let open API.Data in let open Coq_elpi_utils in
  match run ~tactic_mode ~static_check program_ast query_ast
  with
  | API.Execute.Failure -> CErrors.user_err Pp.(str "elpi fails")
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
      let _, sigma = Coq_elpi_HOAS.get_global_env_sigma state in
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
    List.iter (fun (dbname,ast) ->
      let unit = EC.unit ~elpi ~flags:(cc_flags()) ast in
      accumulate_to_db dbname [unit]) clauses_to_add
;;

let run_in_program ?(program = current_program ()) (loc, query) =
  let _ = ensure_initialized () in
  let program_ast = get program in
  let query_ast = `Ast (parse_goal loc query) in
  run_and_print ~tactic_mode:false ~print:true ~static_check:true program_ast query_ast
;;

let typecheck_program ?(program = current_program ()) () =
  let program_ast = get program in
  let query_ast = parse_goal (API.Ast.Loc.initial "(typecheck)") "true." in
  let elpi = ensure_initialized () in
  let program = EC.assemble ~elpi program_ast in
  let query = EC.query program query_ast in
  API.Setup.trace !trace_options;
  run_static_check query
;;


let to_arg = function
  | Int n -> Coq_elpi_goal_HOAS.Int n
  | String x -> Coq_elpi_goal_HOAS.String x
  | Qualid x -> Coq_elpi_goal_HOAS.String (String.concat "." x)
  | DashQualid x -> Coq_elpi_goal_HOAS.String ("-" ^ String.concat "." x)
  | Term g -> Coq_elpi_goal_HOAS.Term g
  | RecordDecl t -> Coq_elpi_goal_HOAS.RecordDecl t

let mainc = ET.Constants.declare_global_symbol "main"

let run_program loc name args =
  let args = args
    |> List.map (glob_arg (Genintern.empty_glob_sign (Global.env())))
    |> List.map (interp_arg (Ltac_plugin.Tacinterp.default_ist ()) Evd.({ sigma = from_env (Global.env()); it = 0 }))
    |> List.map snd in
  let args = args |> List.map to_arg in
  let query ~depth state =
    let state, args = CList.fold_left_map
      (Coq_elpi_goal_HOAS.in_elpi_global_arg ~depth (Coq_elpi_HOAS.mk_coq_context state))
      state args in
    state, (Coq_elpi_utils.of_coq_loc loc, ET.mkApp mainc (EU.list_to_lp_list args) []) in
  let program_ast = get name in
  run_and_print ~tactic_mode:false ~print:false ~static_check:false program_ast (`Fun query)
;;

let mk_trace_opts start stop preds =
  [ "-trace-on"
  ; "-trace-at"; "run"; string_of_int start; string_of_int stop
  ; "-trace-only"; "run"
  ; "-trace-only"; "select"
  ; "-trace-only"; "assign"
  ; "-trace-maxbox"; "30"
  ] @ List.(flatten (map (fun x -> ["-trace-only-pred"; x]) preds))

let trace start stop preds opts =
  if start = 0 && stop = 0 then trace_options := []
  else trace_options := mk_trace_opts start stop preds @ opts

let main_quotedc = ET.Constants.declare_global_symbol "main-quoted"

let print name args =
  let args, fname =
    let default_fname = String.concat "." name ^ ".html" in
    let default_blacklist = [
      "elaborator.elpi";"reduction.elpi";
      "coq-builtin.elpi";"coq-lib.elpi";"coq-HOAS.elpi"
    ] in
    match args with
    | [] -> default_blacklist, default_fname
    | [x] -> default_blacklist, x
    | x :: xs -> xs, x in
  let args = List.map API.RawOpaqueData.of_string args in
  let program_ast = get name in
  let query_ast = parse_goal (API.Ast.Loc.initial "(print)") "true." in
  let elpi = ensure_initialized () in
  let program = EC.assemble ~elpi program_ast in
  let query = EC.query program query_ast in
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
    state, (loc,q) in
  run_and_print ~tactic_mode:false ~print:false ~static_check:false [printer ()] (`Fun q)
;;

open Proofview
open Tacticals.New

let run_tactic loc program ist args =
  let args = List.map to_arg args in
  let loc = Coq_elpi_utils.of_coq_loc loc in
  Goal.enter begin fun gl ->
  tclBIND tclEVARMAP begin fun sigma -> 
  tclBIND tclENV begin fun env -> 
  let k = Goal.goal gl in
  let query = `Fun (Coq_elpi_HOAS.goal2query env sigma k loc ?main:None args ~in_elpi_arg:Coq_elpi_goal_HOAS.in_elpi_arg) in
  let program_ast = get program in
  match run ~tactic_mode:true ~static_check:false program_ast query with
  | API.Execute.Success solution ->
       Coq_elpi_HOAS.tclSOLUTION2EVD solution
  | API.Execute.NoMoreSteps -> tclZEROMSG Pp.(str "elpi run out of steps")
  | _ -> tclZEROMSG Pp.(str "elpi fails")
end end end

let run_in_tactic ?(program = current_program ()) (loc,query) ist args =
  let args = List.map to_arg args in
  Goal.enter begin fun gl ->
  tclBIND tclEVARMAP begin fun sigma ->
  tclBIND tclENV begin fun env -> 
  let k = Goal.goal gl in
  let query = `Fun (Coq_elpi_HOAS.goal2query env ~main:query sigma k loc args ~in_elpi_arg:Coq_elpi_goal_HOAS.in_elpi_arg) in
  let program_ast = get program in
  match run ~tactic_mode:true ~static_check:true program_ast query with
  | API.Execute.Success solution ->
       Coq_elpi_HOAS.tclSOLUTION2EVD solution
  | API.Execute.NoMoreSteps -> tclZEROMSG Pp.(str "elpi run out of steps")
  | _ -> tclZEROMSG Pp.(str "elpi fails")
end end end


let accumulate_files ?(program=current_program()) s =
  let elpi = ensure_initialized () in
  try
    let new_src_ast = List.map (fun fname ->
      File {
        fname;
        fast = unit_from_string ~elpi (API.Ast.Loc.initial fname) ({|accumulate "|} ^ Filename.chop_extension fname ^ {|".|})
      }) s in
    accumulate program new_src_ast
  with Failure s ->  CErrors.user_err Pp.(str s)
 ;;

let accumulate_string ?(program=current_program()) (loc,s) =
  let elpi = ensure_initialized () in
  let new_ast = unit_from_string ~elpi loc s in
  if db_exists program then
    accumulate_to_db program [new_ast]
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
