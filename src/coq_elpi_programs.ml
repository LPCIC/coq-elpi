(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
module EC = API.Compile
module EP = API.Parse

open Coq_elpi_utils
type program_name = Loc.t * qualified_name

let debug_vars = Summary.ref ~name:"elpi-debug" EC.StrSet.empty

let cc_flags () =
  { EC.default_flags with EC.defined_variables = !debug_vars }

let source_cache1 = Summary.ref ~local:true ~name:"elpi-units1" Names.KNmap.empty
let source_cache2 = Summary.ref ~local:true ~name:"elpi-units2" CString.Map.empty

let last_kn = ref None

let in_source : Names.Id.t -> string option * EC.compilation_unit * EC.flags -> Libobject.obj =
  let open Libobject in
  let cache ((_,kn), (hash,u,cf)) =
    last_kn := Some kn;
    source_cache1 := Names.KNmap.add kn (u,cf) !source_cache1;
    hash |> Option.iter (fun hash -> source_cache2 := CString.Map.add hash kn !source_cache2);
  in
  let import _ (_, s as o) = cache o in
  declare_named_object @@ { (default_object "ELPI-UNITS") with
    subst_function =(fun _ -> CErrors.user_err Pp.(str"elpi: No functors"));
    load_function  = import;
    cache_function  = cache;
    open_function = simple_open import;
    discharge_function = (fun o -> Some o);
  }
;;

type cunit = Names.KerName.t * EC.compilation_unit
let dig = ref 0

let intern_unit (hash,u,flags) =
  let id = Names.Id.of_string_soft
    (match hash with Some x -> x | None -> incr dig; string_of_int !dig) in
  last_kn := None;
  Lib.add_leaf (in_source id (hash,u,flags));
  let kn = Option.get !last_kn in
  let u,_ = Names.KNmap.find kn !source_cache1 in
  kn,u

(* Source files can be large, and loaded multiple times since many entry point
   can be implemented in the same file. We share (in memory) the parsed file. *)
let unit_from_ast ~elpi ~flags h ast =
  try
    let u = EC.unit ~elpi ~flags ast in
    intern_unit (h,u,flags)
  with EC.CompileError(oloc, msg) ->
    let loc = Option.map Coq_elpi_utils.to_coq_loc oloc in
    CErrors.user_err ?loc Pp.(str (Option.default "" @@ Option.map API.Ast.Loc.show oloc) ++ cut () ++ str msg)

let unit_from_file ~elpi x : cunit =
  let flags = cc_flags () in
  let hash = Digest.(to_hex @@ file (EP.resolve_file ~elpi ~unit:x ())) in
  try
    let kn = CString.Map.find hash !source_cache2 in
    let u,cf = Names.KNmap.find kn !source_cache1 in
    if flags <> cf then raise Not_found; (* TODO ERROR *)
    kn,u
  with Not_found ->
    try
      let program = EP.program ~elpi ~files:[x] in
      unit_from_ast ~elpi ~flags (Some hash) program
    with
    | Sys_error msg ->
      CErrors.user_err (Pp.str msg)
    | EP.ParseError(oloc, msg) ->
      let loc = Coq_elpi_utils.to_coq_loc oloc in
      CErrors.user_err ~loc Pp.(str (API.Ast.Loc.show oloc) ++ cut () ++ str msg)

let unit_from_string ~elpi loc x : cunit =
  let flags = cc_flags () in
  let hash = Digest.(to_hex @@ string x) in
  try (* TODO: ERROR SAME HASH *)
    let ast = EP.program_from ~elpi ~loc (Lexing.from_string x) in
    unit_from_ast ~elpi ~flags (Some hash) ast
  with
  | EP.ParseError(oloc, msg) ->
    let loc = Coq_elpi_utils.to_coq_loc loc in
    CErrors.user_err ~loc Pp.(str (API.Ast.Loc.show oloc) ++ str msg)

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

module SLMap = Map.Make(struct type t = qualified_name let compare = compare_qualified_name end)
module SLSet = Set.Make(struct type t = qualified_name let compare = compare_qualified_name end)


type src =
| File of src_file
| EmbeddedString of src_string
| Database of qualified_name
and src_file = {
  fname : string;
  fast : cunit;
}
and src_string = {
  sloc : API.Ast.Loc.t;
  sdata : string;
  sast : cunit;
}

let alpha = 65599
let combine_hash h1 h2 = h1 * alpha + h2

let hash_cunit (kn,_) = Names.KerName.hash kn

let hash_list f z l = List.fold_left (fun acc x -> combine_hash (f x) acc) z l

module Chunk = struct
type t =
| Base of {
  hash : int;
  base : cunit;
}
| Snoc of {
  source_rev : cunit list;
  prev : t;
  hash : int
}
let hash = function
| Base { hash } -> hash
| Snoc { hash } -> hash

let snoc source_rev prev =
let hash = (hash_list hash_cunit (hash prev) source_rev) in
Snoc { hash; prev; source_rev }

let eq x y = x == y
end

module Code = struct
type 'db t =
| Base of {
  hash : int;
  base : cunit;
}
| Snoc of {
  source : cunit;
  prev : 'db t;
  hash : int;
  cacheme: bool;
}
| Snoc_db of {
  chunks : 'db;
  prev : 'db t;
  hash : int
}
let hash = function
| Base { hash } -> hash
| Snoc { hash } -> hash
| Snoc_db { hash } -> hash

let cache = function
| Base _ -> true
| Snoc { cacheme } -> cacheme
| Snoc_db _ -> false

let snoc source prev =
let hash = combine_hash (hash prev) (hash_cunit source) in
Snoc { hash; prev; source; cacheme = cache prev }

let snoc_opt source prev =
match prev with
| Some prev -> snoc source prev
| None -> Base { hash = (hash_cunit source); base = source }

let snoc_db f chunks prev =
let hash = hash prev in
let hash = combine_hash (f chunks) hash in
Snoc_db { hash; prev; chunks }
   
let snoc_db_opt chunks prev =
match prev with
| Some prev -> snoc_db (fun _ -> 0) chunks prev
| None -> assert false

let rec map f = function
| Base x -> Base x
| Snoc { prev; source; cacheme = true } ->
    (* no need to map, since prev is constant *)
    let prev = Obj.magic prev in
    snoc source prev
| Snoc { prev; source } ->
    let prev = map f prev in
    snoc source prev
| Snoc_db { prev; chunks } ->
    let prev = map f prev in
    let chunks = f chunks in
    snoc_db Chunk.hash chunks prev

let rec eq c x y =
  x == y ||
  match x,y with
  | Base x, Base y -> Names.KerName.equal (fst x.base) (fst y.base)
  | Snoc x, Snoc y -> Names.KerName.equal (fst x.source) (fst y.source) && eq c x.prev y.prev
  | Snoc_db x, Snoc_db y -> c x.chunks y.chunks && eq c x.prev y.prev
  | _ -> false

end

type db = {
  sources_rev : Chunk.t;
  units : Names.KNset.t;
}

type nature = Command of { raw_args : bool } | Tactic | Program of { raw_args : bool } 

let current_program = Summary.ref ~name:"elpi-cur-program-name" None


type program = {
  sources_rev : qualified_name Code.t;
  units : Names.KNset.t;
  dbs : SLSet.t;
}

let program_name : nature SLMap.t ref =
  Summary.ref ~stage:Summary.Stage.Synterp ~name:"elpi-programs-synterp" SLMap.empty

let program_src : program SLMap.t ref =
  Summary.ref ~name:"elpi-programs" SLMap.empty

let program_exists name = SLMap.mem name !program_name

let db_name : SLSet.t ref = Summary.ref ~stage:Summary.Stage.Synterp  ~name:"elpi-db-synterp" SLSet.empty
let db_name_src : db SLMap.t ref = Summary.ref ~name:"elpi-db" SLMap.empty
let db_exists name = SLSet.mem name !db_name

(* Setup called *)
let elpi = Stdlib.ref None

let elpi_builtins =
  API.BuiltIn.declare
    ~file_name:"elpi-builtin.elpi"
    Elpi.Builtin.(
      core_builtins @
      elpi_builtins @
      elpi_nonlogical_builtins @
      elpi_stdlib @
      elpi_map @
      elpi_set @
      io_builtins @
      ocaml_runtime @
      lp_builtins @
      []
    )

let coq_builtins =
  API.BuiltIn.declare
    ~file_name:"coq-builtin.elpi"
    Coq_elpi_builtins.coq_builtins

let file_resolver =
  let error_cannot_resolve dp file =
    raise (Failure (
      "Cannot resolve " ^  Names.DirPath.to_string dp ^
      " in loadpath:\n" ^ String.concat "\n" (List.map (fun t ->
      "- " ^ Names.DirPath.to_string (Loadpath.logical t) ^
      " -> " ^ Loadpath.physical t) (Loadpath.get_load_paths ())))) in
  let error_found_twice logpath file abspath other =
    raise (Failure (
      "File " ^ file ^ " found twice in loadpath " ^ logpath ^ ":\n" ^
      "- " ^ abspath ^ "\n- " ^ other ^ "\n")) in
  let error_file_not_found logpath file paths =
    raise (Failure (
      "File " ^ file ^ " not found in loadpath " ^ logpath ^ ", mapped to:\n" ^
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
let get_nature p =
  try SLMap.find p !program_name
  with Not_found ->
    CErrors.user_err
      Pp.(str "No Elpi Program named " ++ pr_qualified_name p)

let get ?(fail_if_not_exists=false) p =
  let _elpi = ensure_initialized () in
  let nature = get_nature p in
  try
  let { sources_rev; units; dbs } = SLMap.find p !program_src in
  units, dbs, Some nature, Some sources_rev
  with Not_found ->
  if fail_if_not_exists then
    CErrors.user_err
      Pp.(str "No Elpi Program named " ++ pr_qualified_name p)
  else
    Names.KNset.empty, SLSet.empty, None, None

let code n : Chunk.t Code.t =
  let _,_,_,sources = get n in
  match sources with 
  | None -> CErrors.user_err Pp.(str "Unknown Program " ++ str (show_qualified_name n))
  | Some sources -> sources |> Code.map (fun name ->
  try
    let { sources_rev } : db = SLMap.find name !db_name_src in
    sources_rev
  with
    Not_found ->
      CErrors.user_err Pp.(str "Unknown Db " ++ str (show_qualified_name name)))

let in_program_name : qualified_name * nature -> Libobject.obj =
  let open Libobject in
  declare_object @@ { (superglobal_object_nodischarge "ELPI_synterp"
  ~cache:(fun (name,nature) ->
    program_name := SLMap.add name nature !program_name)
  ~subst:(Some (fun _ -> CErrors.user_err Pp.(str"elpi: No functors yet"))))
  with object_stage = Summary.Stage.Synterp }

let append_to_prog name src =
  let units, dbs, _, prog = get name in
  let units, dbs, prog =
    match src with
    (* undup *)
    | File { fast = (kn,_) } when Names.KNset.mem kn units -> units, dbs, prog
    | EmbeddedString { sast = (kn,_) } when Names.KNset.mem kn units -> units, dbs, prog
    | Database n  when SLSet.mem n dbs -> units, dbs, prog
    (* add *)
    | File { fast = (kn,_ as u) } -> (Names.KNset.add kn units), dbs, Some (Code.snoc_opt u prog)
    | EmbeddedString { sast = (kn,_ as u) } -> (Names.KNset.add kn units), dbs, Some (Code.snoc_opt u prog)
    | Database n ->  units, SLSet.add n dbs, Some (Code.snoc_db_opt n prog)
    in
  let prog = Option.get prog in
  { units; dbs; sources_rev = prog }

let in_program : qualified_name * src -> Libobject.obj =
  let open Libobject in
  declare_object @@ superglobal_object_nodischarge "ELPI"
  ~cache:(fun (name,src_ast) ->
    program_src :=
      SLMap.add name (append_to_prog name src_ast) !program_src)
  ~subst:(Some (fun _ -> CErrors.user_err Pp.(str"elpi: No functors yet")))


let declare_program name nature =
  let obj = in_program_name (name,nature) in
  Lib.add_leaf obj

let init_program name u =
  let obj = in_program (name, u) in
  Lib.add_leaf obj
;;

let add_to_program name v =
  let obj = in_program (name, v) in
  Lib.add_leaf obj
;;

let append_to_db name kname c =
  try
    let (db : db) = SLMap.find name !db_name_src in
    if Names.KNset.mem kname db.units then db
    else { sources_rev = Chunk.snoc c db.sources_rev; units = Names.KNset.add kname db.units }
  with Not_found ->
  match c with
  | [] -> assert false
  | [base] ->
      { sources_rev = Chunk.Base { hash = hash_cunit base; base }; units = Names.KNset.singleton kname }
  | _ -> assert false

type snippet = {
  program : qualified_name;
  code :cunit list;
  scope : Coq_elpi_utils.clause_scope;
  vars : Names.Id.t list;
}

let in_db : Names.Id.t -> snippet -> Libobject.obj =
  let open Libobject in
  let cache ((_,kn),{ program = name; code = p; _ }) =
    db_name_src := SLMap.add name (append_to_db name kn p) !db_name_src in
  let import i (_,s as o) = if Int.equal i 1 || s.scope =  Coq_elpi_utils.SuperGlobal then cache o in
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

let in_db_name : qualified_name -> Libobject.obj =
  let open Libobject in
  declare_object @@ {
    (superglobal_object_nodischarge "ELPI-DB_synterp"
       ~cache:(fun name -> db_name := SLSet.add name !db_name)
       ~subst:(Some (fun _ -> CErrors.user_err Pp.(str"elpi: No functors yet"))))
      with
        object_stage = Summary.Stage.Synterp }

let declare_db program =
  ignore @@ Lib.add_leaf (in_db_name program)

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

let declare_program (loc,qualid) nature =
  if program_exists qualid || db_exists qualid then
    CErrors.user_err Pp.(str "Program/Tactic/Db " ++ pr_qualified_name qualid ++ str " already exists")
  else
    declare_program qualid nature
  
let init_program (loc,qualid) (init : src) =
  if Global.sections_are_opened () then
    CErrors.user_err Pp.(str "Program/Tactic/Db cannot be declared inside sections")
  else
    init_program qualid init

let declare_db (loc,qualid) =
  if program_exists qualid || db_exists qualid then
    CErrors.user_err Pp.(str "Program/Tactic/Db " ++ pr_qualified_name qualid ++ str " already exists")
  else
    declare_db qualid

let init_db (loc,qualid) (init : cunit) =
  if Global.sections_are_opened () then
    CErrors.user_err Pp.(str "Program/Tactic/Db cannot be declared inside sections")
  else if match Global.current_modpath () with Names.ModPath.MPdot (Names.ModPath.MPfile _,_) -> true | _ -> false then
    CErrors.user_err Pp.(str "Program/Tactic/Db cannot be declared inside modules")
  else
    add_to_db qualid [init] [] Coq_elpi_utils.SuperGlobal
;;

let set_current_program n =
  let _ = ensure_initialized () in
  current_program := Some n

let current_program () =
  match !current_program with
  | None -> CErrors.user_err Pp.(str "No current Elpi Program")
  | Some x -> x


let lp_checker_ast = Summary.ref ~name:"elpi-lp-checker" None
let in_lp_checker_ast : cunit list -> Libobject.obj =
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
  | Some l -> List.map snd l

let lp_printer_ast = Summary.ref ~name:"elpi-lp-printer" None
let in_lp_printer_ast : cunit -> Libobject.obj =
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
  | Some l -> snd l

let accumulate p (v : src list) =
  if not (program_exists p) then
    CErrors.user_err Pp.(str "No Elpi Program named " ++ pr_qualified_name p);
  v |> List.iter (add_to_program p)

let accumulate_to_db p v vs ~scope =
  if not (db_exists p) then
    CErrors.user_err Pp.(str "No Elpi Db " ++ pr_qualified_name p);
  add_to_db p v vs scope

let group_clauses l =
  let rec aux acc l =
    match acc, l with
    | _, [] -> List.rev acc
    | [], (dbname,ast,vs,scope) :: xs ->  aux [dbname,[ast],vs,scope] xs
    | (dbname,asts,vs,scope) :: tl as acc, (dbname1,ast,vs1,scope1) :: xs ->
        if dbname = dbname1 && vs = vs1 && scope = scope1 then
          aux ((dbname,asts@[ast],vs,scope) :: tl) xs
        else
          aux ((dbname1,[ast],vs1,scope1) :: acc) xs
    in
      aux [] l
  
let () = Coq_elpi_builtins.set_accumulate_to_db (fun clauses_to_add ->
  let elpi = ensure_initialized () in
  let flags = cc_flags () in
  let clauses_to_add = clauses_to_add |> group_clauses |>
    List.map (fun (dbname,asts,vs,scope) ->
      let units = List.map (unit_from_ast ~elpi ~flags None) asts in
      dbname,units,vs,scope) in
  clauses_to_add |> List.iter (fun (dbname,units,vs,scope) ->
    accumulate_to_db dbname units vs ~scope))
  
let () = Coq_elpi_builtins.set_accumulate_text_to_db (fun n txt scope ->
  let elpi = ensure_initialized () in
  let loc = API.Ast.Loc.initial "(elpi.add_predicate)" in
  let u = unit_from_string ~elpi loc txt in
  accumulate_to_db n [u] [] ~scope)
