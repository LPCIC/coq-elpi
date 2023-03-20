(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
module EC = API.Compile
module EP = API.Parse
module EPP = API.Pp
module EU = API.Utils
module ET = API.RawData

open Coq_elpi_utils

let debug_vars = Summary.ref ~name:"elpi-debug" EC.StrSet.empty

let cc_flags () =
  { EC.default_flags with EC.defined_variables = !debug_vars }

let source_cache = Summary.Local.ref
  ~name:"elpi-source-cache"
  CString.Map.empty

(* Source files can be large, and loaded multiple times since many entry point
   can be implemented in the same file. We share (in memory) the parsed file. *)
let unit_from_file ~elpi x =
  let open Summary.Local in
  let flags = cc_flags () in
  try
    let hash = Digest.file (EP.resolve_file ~elpi ~unit:x ()) in
    let u, old_flags, old_hash = CString.Map.find x !source_cache in
    if flags <> old_flags then raise Not_found;
    if hash <> old_hash then raise Not_found;
    u
  with Not_found ->
    try
      let hash = Digest.file (EP.resolve_file ~elpi ~unit:x ()) in
      let program = EP.program ~elpi ~files:[x] in
      let u = EC.unit ~elpi ~flags program in
      source_cache := CString.Map.add x (u,flags,hash) !source_cache;
      u
    with
    | Sys_error msg ->
      CErrors.user_err (Pp.str msg)
    | EP.ParseError(oloc, msg) ->
      let loc = Coq_elpi_utils.to_coq_loc oloc in
      CErrors.user_err ~loc Pp.(str (API.Ast.Loc.show oloc) ++ cut () ++ str msg)
    | EC.CompileError(oloc, msg) ->
      let loc = Option.map Coq_elpi_utils.to_coq_loc oloc in
      CErrors.user_err ?loc Pp.(str (Option.default "" @@ Option.map API.Ast.Loc.show oloc) ++ cut () ++ str msg)

let unit_from_string ~elpi loc x =
  try EC.unit ~elpi ~flags:(cc_flags ()) (EP.program_from ~elpi ~loc (Lexing.from_string x))
  with
  | EP.ParseError(oloc, msg) ->
    let loc = Coq_elpi_utils.to_coq_loc loc in
    CErrors.user_err ~loc Pp.(str (API.Ast.Loc.show oloc) ++ str msg)
  | EC.CompileError(oloc, msg) ->
    let loc = Option.map Coq_elpi_utils.to_coq_loc oloc in
    CErrors.user_err ?loc Pp.(str (Option.default "" @@ Option.map API.Ast.Loc.show oloc) ++ str msg)

let parse_goal ~elpi loc text =
  try EP.goal ~elpi ~loc ~text
  with EP.ParseError(oloc, msg) ->
    let loc = Coq_elpi_utils.to_coq_loc oloc in
    CErrors.user_err ~loc Pp.(str (API.Ast.Loc.show oloc) ++ str msg)

let assemble_units ~elpi units =
  try EC.assemble ~elpi ~flags:(cc_flags ()) units
  with EC.CompileError(oloc, msg) ->
    let loc = Option.map Coq_elpi_utils.to_coq_loc oloc in
    CErrors.user_err ?loc Pp.(str (Option.default "" @@ Option.map API.Ast.Loc.show oloc) ++ str msg)

let extend_w_units ~base units =
  try EC.extend ~flags:(cc_flags ()) ~base units
  with EC.CompileError(oloc, msg) ->
    let loc = Option.map Coq_elpi_utils.to_coq_loc oloc in
    CErrors.user_err ?loc Pp.(str (Option.default "" @@ Option.map API.Ast.Loc.show oloc) ++ str msg)

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
type nature = Command of { raw_args : bool } | Tactic | Program of { raw_args : bool } 

  val get : qualified_name -> Compile.compilation_unit list * Compile.compilation_unit list (* code , db *)
  val get_nature : qualified_name -> nature

  val create_program : program_name -> nature -> src -> unit
  val create_db : program_name -> src -> unit

  val set_current_program : qualified_name -> unit
  val current_program : unit -> qualified_name
  val accumulate : qualified_name -> src list -> unit
  val accumulate_to_db : qualified_name -> Compile.compilation_unit -> Names.Id.t list -> scope:Coq_elpi_utils.clause_scope -> unit

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
  fast : EC.compilation_unit
}
and src_string = {
  sloc : API.Ast.Loc.t;
  sdata : string;
  sast : EC.compilation_unit
}
type nature = Command of { raw_args : bool } | Tactic | Program of { raw_args : bool } 
let compare_src = Stdlib.compare

module SrcSet = Set.Make(struct type t = src let compare = compare_src end)

let current_program = Summary.ref ~name:"elpi-cur-program-name" None

let program_src : (SrcSet.t * nature * src list) SLMap.t ref =
  Summary.ref ~name:"elpi-programs" SLMap.empty
let program_exists name = SLMap.mem name !program_src

module KSet = Set.Make(Names.KerName)
type db = {
  base : EC.compilation_unit;
  extensions : KSet.t;
  contents : (Names.KerName.t * EC.compilation_unit) list;
}

let db_name_src : db SLMap.t ref =
  Summary.ref ~name:"elpi-db" SLMap.empty
let db_exists name = SLMap.mem name !db_name_src

let ast_of_src = function
  | File { fast = a } -> [`Static,(a)]
  | EmbeddedString { sast = a } -> [`Static,(a)]
  | Database name ->
     try
       let { base; contents } = SLMap.find name !db_name_src in
        (`Static,(base)) :: List.map (fun (_,x) -> `Dynamic,x) contents
     with Not_found ->
       CErrors.user_err Pp.(str "Unknown Db " ++ str (show_qualified_name name))

(* Setup called *)
let elpi = Stdlib.ref None

let elpi_builtins =
  API.BuiltIn.declare
    ~file_name:"elpi-builtin.elpi"
    Elpi.Builtin.(core_builtins @
    elpi_builtins @ elpi_nonlogical_builtins @
    elpi_stdlib @ elpi_map @ elpi_set @
    io_builtins @ ocaml_runtime)

let coq_builtins =
  API.BuiltIn.declare
    ~file_name:"coq-builtin.elpi"
    Coq_elpi_builtins.coq_builtins

let file_resolver =
  let error_cannot_resolve dp file =
    raise (Failure ("Cannot resolve " ^  Names.DirPath.to_string dp ^
    " in loadpath:\n" ^ String.concat "\n" (List.map (fun t ->
        "- " ^ Names.DirPath.to_string (Loadpath.logical t) ^
          " -> " ^ Loadpath.physical t) (Loadpath.get_load_paths ())))) in
  let error_found_twice logpath file abspath other =
    raise (Failure ("File " ^ file ^ " found twice in loadpath " ^ logpath ^ ":\n" ^
      "- " ^ abspath ^ "\n- " ^ other ^ "\n")) in
  let error_file_not_found logpath file paths =
    raise (Failure ("File " ^ file ^ " not found in loadpath " ^ logpath ^ ", mapped to:\n" ^
      String.concat "\n" (List.map (fun t -> "- " ^ t) paths))) in
  let ensure_only_one_path_contains logpath file (paths as allpaths) =
    let rec aux found paths =
      match paths, found with
      | [], None -> error_file_not_found logpath file allpaths
      | [], Some abspath -> abspath
      | x :: xs, None ->
          let abspath = x ^ "/" ^ file in
          if Sys.file_exists abspath then aux (Some abspath) xs
          else aux None xs
      | x :: xs, Some other ->
          let abspath = x ^ "/" ^ file in
          if Sys.file_exists abspath then error_found_twice logpath file abspath other
          else aux found xs
    in
      aux None paths in 
  let legacy_paths = 
      let build_dir = Coq_elpi_config.elpi_dir in
      let installed_dirs =
        let valid_dir d = try Sys.is_directory d with Sys_error _ -> false in
        let user_contrib =
          if Sys.backend_type = Sys.Other "js_of_ocaml" then "../.."
          else
            let env = Boot.Env.init () in
            Boot.Env.(user_contrib env |> Path.to_string) in
        user_contrib :: Envars.coqpath
        |> List.map (fun p -> p ^ "/elpi/")
        |> ((@) [".";".."]) (* Hem, this sucks *)
        |> List.filter valid_dir
      in
      "." :: build_dir :: installed_dirs in
  let legacy_resolver = API.Parse.std_resolver ~paths:legacy_paths () in
  fun ?cwd ~unit:file () ->
    if Str.(string_match (regexp_string "coq://") file 0) then
      let logpath_file = String.(sub file 6 (length file - 6)) in
      match string_split_on_char '/' logpath_file with
      | [] -> assert false
      | logpath :: rest ->
          let dp = string_split_on_char '.' logpath |> CList.rev_map Names.Id.of_string_soft |> Names.DirPath.make in
          match Loadpath.find_with_logical_path dp with
          | _ :: _ as paths ->
              let paths = List.map Loadpath.physical paths in
              ensure_only_one_path_contains logpath (String.concat "/" rest) paths
          | [] -> error_cannot_resolve dp file
    else legacy_resolver ?cwd ~unit:file ()
;;

let init () =
  let e = API.Setup.init ~builtins:[coq_builtins;elpi_builtins] ~file_resolver () in
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
  try
    let src, nature, ast = SLMap.find p !program_src in
    src, Some nature, ast
  with Not_found ->
    if fail_if_not_exists then
      CErrors.user_err
        Pp.(str "No Elpi Program named " ++ pr_qualified_name p)
    else
      SrcSet.empty, None, []

let nature_max old_nature nature =
  match old_nature with
  | Some x -> x
  | None ->
      match nature with
      | None -> CErrors.anomaly Pp.(str "nature_max")
      | Some x -> x

let append_to_prog name nature l =
  let seen, old_nature, prog = get name in
  let nature = nature_max old_nature nature in
  let rec aux seen acc = function
    | [] -> seen, List.rev acc
    | x :: xs when SrcSet.mem x seen -> aux seen acc xs
    | x :: xs -> aux (SrcSet.add x seen) (x :: acc) xs in
  let seen, l = aux seen [] l in
  let prog = prog @ l in
  seen, nature, prog

let in_program : qualified_name * nature option * src list -> Libobject.obj =
  let open Libobject in
  declare_object @@ superglobal_object_nodischarge "ELPI"
    ~cache:(fun (name,nature,src_ast) ->
      program_src :=
        SLMap.add name (append_to_prog name nature src_ast) !program_src)
    ~subst:(Some (fun _ -> CErrors.user_err Pp.(str"elpi: No functors yet")))

let init_program name nature =
  let obj = in_program (name, Some nature, []) in
  Lib.add_leaf obj
;;

let add_to_program name v =
  let obj = in_program (name, None, v) in
  Lib.add_leaf obj
;;

let append_to_db name (kname,data as l) =
  try
      let db = SLMap.find name !db_name_src in
      if KSet.mem kname db.extensions then db
      else { db with contents = db.contents @ [l];
                    extensions = KSet.add kname db.extensions }
  with Not_found ->
    (* We assume the first chunk is the base *)
    let extensions = KSet.singleton kname in
    { base = data; extensions; contents = [];}

type snippet = {
  program : qualified_name;
  code : EC.compilation_unit;
  scope : Coq_elpi_utils.clause_scope;
  vars : Names.Id.t list;
}

let in_db : Names.Id.t -> snippet -> Libobject.obj =
  let open Libobject in
  let cache ((_,kname), { program = name; code = p; _ }) =
    db_name_src := SLMap.add name (append_to_db name (kname,p)) !db_name_src in
  let import i (_, s as o) = if Int.equal i 1 || s.scope =  Coq_elpi_utils.SuperGlobal then cache o in
  declare_named_object @@ { (default_object "ELPI-DB") with
    classify_function = (fun { scope; program; _ } ->
      match scope with
      | Coq_elpi_utils.Local -> Dispose
      | Coq_elpi_utils.Regular -> Substitute
      | Coq_elpi_utils.Global -> Keep
      | Coq_elpi_utils.SuperGlobal -> Keep);
    load_function  = import;
    cache_function  = cache;
    subst_function = (fun (_,o) -> o);
    open_function = simple_open import;
    discharge_function = (fun (({ scope; program; vars; } as o)) ->
      if scope = Coq_elpi_utils.Local || (List.exists (fun x -> Lib.is_in_section (Names.GlobRef.VarRef x)) vars) then None
      else Some o);

}

let accum = ref 0
let add_to_db program code vars scope =
  ignore @@ Lib.add_leaf
    (in_db (Names.Id.of_string (incr accum; Printf.sprintf "_ELPI_%d" !accum)) { program; code; scope; vars })

let lp_command_ast = Summary.ref ~name:"elpi-lp-command" None
let in_lp_command_src : src -> Libobject.obj =
  let open Libobject in
  declare_object { (default_object "ELPI-LP-COMMAND") with
    load_function = (fun _ x -> lp_command_ast := Some x);
}
let load_command s =
  let elpi = ensure_initialized () in
  let ast = File {
    fname = s;
    fast = unit_from_file ~elpi s
  } in
  lp_command_ast := Some ast;
  Lib.add_leaf (in_lp_command_src ast)
let command_init () =
  match !lp_command_ast with
  | None -> CErrors.user_err Pp.(str "Elpi CommandTemplate was not called")
  | Some ast -> ast

let lp_tactic_ast = Summary.ref ~name:"elpi-lp-tactic" None
let in_lp_tactic_ast : src -> Libobject.obj =
  let open Libobject in
  declare_object { (default_object "ELPI-LP-TACTIC") with
    load_function = (fun _ x -> lp_tactic_ast := Some x);
}
let load_tactic s =
  let elpi = ensure_initialized () in
  let ast = File {
    fname = s;
    fast = unit_from_file ~elpi s
  } in
  lp_tactic_ast := Some ast;
  Lib.add_leaf (in_lp_tactic_ast ast)
let tactic_init () =
  match !lp_tactic_ast with
  | None -> CErrors.user_err Pp.(str "Elpi TacticTemplate was not called")
  | Some ast -> ast

let create_program (loc,qualid) nature init =
  if program_exists qualid || db_exists qualid then
    CErrors.user_err Pp.(str "Program/Tactic/Db " ++ pr_qualified_name qualid ++ str " already exists")
  else if Global.sections_are_opened () then
    CErrors.user_err Pp.(str "Program/Tactic/Db cannot be declared inside sections")
  else
    let () = init_program qualid nature in
    add_to_program qualid [init]

let create_db (loc,qualid) init =
  if program_exists qualid || db_exists qualid then
    CErrors.user_err Pp.(str "Program/Tactic/Db " ++ pr_qualified_name qualid ++ str " already exists")
  else if Global.sections_are_opened () then
    CErrors.user_err Pp.(str "Program/Tactic/Db cannot be declared inside sections")
  else if match Global.current_modpath () with Names.ModPath.MPdot (Names.ModPath.MPfile _,_) -> true | _ -> false then
    CErrors.user_err Pp.(str "Program/Tactic/Db cannot be declared inside modules")
  else
    match ast_of_src init with
    | [`Static,base] -> add_to_db qualid base [] Coq_elpi_utils.SuperGlobal
    | _ -> assert false
;;

let set_current_program n =
  let _ = ensure_initialized () in
  current_program := Some n

let current_program () =
  match !current_program with
  | None -> CErrors.user_err Pp.(str "No current Elpi Program")
  | Some x -> x

let rec static_prefix acc = function
  | [] -> List.rev acc, []
  | (`Static,l) :: rest -> static_prefix (l :: acc) rest
  | rest when List.for_all (fun (tag,_) -> tag = `Dynamic) rest -> List.rev acc, List.map snd rest
  | rest -> List.rev_append acc (List.map snd rest), []

let get_nature x =
  Option.get @@ Util.pi2 (get ~fail_if_not_exists:true x)
  
let get x =
  let chunks = List.(flatten @@ map ast_of_src (Util.pi3 (get ~fail_if_not_exists:true x))) in
  static_prefix [] chunks

let lp_checker_ast = Summary.ref ~name:"elpi-lp-checker" None
let in_lp_checker_ast : EC.compilation_unit list -> Libobject.obj =
  let open Libobject in
  declare_object { (default_object "ELPI-LP-CHECKER") with
    load_function = (fun _ x -> lp_checker_ast := Some x);
}

let load_checker s =
  let elpi = ensure_initialized () in
  let basic_checker = unit_from_string ~elpi (Elpi.API.Ast.Loc.initial "(elpi-checker)") Elpi.Builtin_checker.code in
  let coq_checker = unit_from_file ~elpi s in
  let p = [basic_checker;coq_checker] in
  Lib.add_leaf (in_lp_checker_ast p)
let checker () =
  match !lp_checker_ast with
  | None -> CErrors.user_err Pp.(str "Elpi Checker was not called")
  | Some ast -> ast

let lp_printer_ast = Summary.ref ~name:"elpi-lp-printer" None
let in_lp_printer_ast : EC.compilation_unit -> Libobject.obj =
  let open Libobject in
  declare_object { (default_object "ELPI-LP-PRINTER") with
    load_function = (fun _ x -> lp_printer_ast := Some x);
}
let load_printer s =
  let elpi = ensure_initialized () in
  let ast = unit_from_file ~elpi s in
  lp_printer_ast := Some ast;
  Lib.add_leaf (in_lp_printer_ast ast)
let printer () =
  match !lp_printer_ast with
  | None -> CErrors.user_err Pp.(str "Elpi Printer was not called")
  | Some ast -> ast

let accumulate p v =
  if not (program_exists p) then
    CErrors.user_err Pp.(str "No Elpi Program named " ++ pr_qualified_name p);
  add_to_program p v

let accumulate_to_db p v vs ~scope =
  if not (db_exists p) then
    CErrors.user_err Pp.(str "No Elpi Db " ++ pr_qualified_name p);
  add_to_db p v vs scope

end

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
  let init = EmbeddedString { sloc = loc; sdata = s; sast = unit} in
  create_db n init

let default_max_step = max_int

let trace_options = Summary.ref ~name:"elpi-trace" []
let max_steps = Summary.ref ~name:"elpi-steps" default_max_step

let debug vl = debug_vars := List.fold_right EC.StrSet.add vl EC.StrSet.empty

let bound_steps n =
  if n <= 0 then max_steps := default_max_step else max_steps := n

(* Units are marshalable, but programs are not *)
let compiler_cache = Summary.Local.ref
  ~name:"elpi-compiler-cache"
  SLMap.empty

let compile name baseul extra =
  try
    let units, base = SLMap.find name (Summary.Local.(!) compiler_cache) in
    if CList.for_all2eq (==) units baseul then extend_w_units ~base extra
    else raise Not_found
  with Not_found ->
    let elpi = ensure_initialized () in
    let program = assemble_units ~elpi baseul in
    (Summary.Local.(:=) compiler_cache (SLMap.add name (baseul,program) (Summary.Local.(!) compiler_cache)));
    extend_w_units ~base:program extra

let () = Coq_elpi_builtins.set_accumulate_to_db (fun n x vs ~scope ->
  let elpi = ensure_initialized () in
  let u =
    try EC.unit ~elpi ~flags:(cc_flags ()) x
    with EC.CompileError(oloc, msg) ->
      let loc = Option.map Coq_elpi_utils.to_coq_loc oloc in
      CErrors.user_err ?loc (Pp.str msg) in
  Programs.accumulate_to_db n u vs ~scope)

let get_and_compile name =
  let core_units, extra_units = get name in
  let prog = compile name core_units extra_units in
  let raw_args =
    match get_nature name with
    | Command { raw_args } -> raw_args
    | Program { raw_args } -> raw_args
    | Tactic -> true in
  prog, raw_args

let run_static_check query =
  let checker = compile ["Elpi";"Typecheck"] (checker()) [] in
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
    List.iter (fun (dbname,ast,vs,scope) ->
      let unit = EC.unit ~elpi ~flags:(cc_flags()) ast in
      accumulate_to_db dbname unit vs ~scope) clauses_to_add
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
    |> List.map (Coq_elpi_arg_HOAS.Cmd.glob (Genintern.empty_glob_sign env))
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
  let program, _ = get_and_compile name in
  let query_ast = parse_goal ~elpi (API.Ast.Loc.initial "(print)") "true." in
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
    state, (loc,q), [] in
  run_and_print ~print:false ~static_check:false ["Elpi";"Print"] (compile ["Elpi";"Print"] [printer ()] []) (`Fun q)
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
    accumulate_to_db program new_ast [] ~scope:Coq_elpi_utils.Regular
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
  if db_exists db then accumulate_to_db db new_ast
  else CErrors.user_err
    Pp.(str "Db " ++ pr_qualified_name db ++ str" not found") 

let loc_merge l1 l2 =
  try Loc.merge l1 l2
  with Failure _ -> l1

let cache_program (nature,p,p_str) =
  match nature with
  | Command _ ->
    Vernacextend.vernac_extend
      ~command:("Elpi"^p_str)
      ~classifier:(fun _ -> Vernacextend.(VtSideff ([], VtNow)))
      ?entry:None
      [ Vernacextend.TyML
          (false,
           Vernacextend.TyNonTerminal
             (Extend.TUentry
                (Genarg.get_arg_tag Coq_elpi_arg_syntax.wit_elpi_loc),
              Vernacextend.TyTerminal
                (p_str,
                 Vernacextend.TyNonTerminal
                   (Extend.TUlist0
                      (Extend.TUentry (Genarg.get_arg_tag Coq_elpi_arg_syntax.wit_elpi_cmd_arg))
                   ,Vernacextend.TyNonTerminal
                       (Extend.TUentry (Genarg.get_arg_tag Coq_elpi_arg_syntax.wit_elpi_loc),
                        Vernacextend.TyNil)))),
           (fun loc0 args loc1 ?loc ~atts () -> Vernacextend.vtdefault (fun () ->
                run_program (Option.default (loc_merge loc0 loc1) loc) p ~atts args)),
           None)
      ]
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

let solve_TC program env sigma depth unique ~best_effort filter =
  let loc = API.Ast.Loc.initial "(unknown)" in
  let atts = [] in
  let glss, _ = Evar.Set.partition (filter sigma) (Evd.get_typeclass_evars sigma) in
  let gls = Evar.Set.elements glss in
  let query ~depth state = 
    let state, (loc, q), gls =
      Coq_elpi_HOAS.goals2query sigma gls loc ~main:(Coq_elpi_HOAS.Solve [])
        ~in_elpi_tac_arg:Coq_elpi_arg_HOAS.in_elpi_tac ~depth state in
    let state, qatts = atts2impl loc ~depth state atts q in
    let state = API.State.set Coq_elpi_builtins.tactic_mode state true in
    state, (loc, qatts), gls
    in
  let cprogram, _ = get_and_compile program in
  match run ~static_check:false cprogram (`Fun query) with
  | API.Execute.Success solution ->
      let sigma, _, _ = Coq_elpi_HOAS.solution2evd sigma solution glss in
      Some(false,sigma)
  | API.Execute.NoMoreSteps -> CErrors.user_err Pp.(str "elpi run out of steps")
  | API.Execute.Failure -> elpi_fails program
  | exception (Coq_elpi_utils.LtacFail (level, msg)) -> elpi_fails program

let override_TC p ql =
  let ql = List.map Coq_elpi_utils.locate_simple_qualid ql in 
  Coq_elpi_class_tactics_hacked.takeover ql (solve_TC p)

(*XXX aggiungere il libobject per il comando di override XXX*)