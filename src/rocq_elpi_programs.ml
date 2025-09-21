(* rocq-elpi: Coq terms as the object language of elpi                       *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
module EC = API.Compile
module EP = API.Parse

open Rocq_elpi_utils
type program_name = Loc.t * qualified_name
type cunit = Full of Names.KerName.t * EC.compilation_unit | Signature of Names.KerName.t * EC.compilation_unit_signature
let name_of_cunit = function Full(_,u) -> EC.compilation_unit_name u | Signature(_,s) -> EC.compilation_unit_signature_name s
type what = Code | SignatureOnly
let pp_cunit fmt = function
  | Full (kn,u) -> Format.fprintf fmt "Full(%s,%s)" Names.KerName.(debug_to_string kn) (EC.compilation_unit_name u)
  | Signature(kn,s) -> Format.fprintf fmt "Signature(%s,%s)" Names.KerName.(debug_to_string kn) (EC.compilation_unit_signature_name s)
let eq_cunit x y =
  match x,y with
  | Full(k1,_), Full(k2,_) -> Names.KerName.equal k1 k2
  | Signature(k1,_), Signature(k2,_) -> Names.KerName.equal k1 k2
  | _ -> false
let kn_of_cunit = function
  | Full (kn,_) | Signature (kn,_) -> kn

[%%if coq = "9.0"]
let my_filtered_open = Libobject.simple_open
let my_simple_open ?cat f = my_filtered_open ?cat (fun i v -> if Int.equal i 1 then f v)
let is_in_section = Lib.is_in_section
[%%else]
let my_filtered_open = Libobject.filtered_open
let my_simple_open = Libobject.simple_open
let is_in_section = Global.is_in_section
[%%endif]


module SLMap = Map.Make(struct type t = qualified_name let compare = compare_qualified_name end)
module SLSet = Set.Make(struct type t = qualified_name let compare = compare_qualified_name end)

type src =
  | File of src_file
  | EmbeddedString of src_string
  | DatabaseBody of qualified_name
  | DatabaseHeader of src_db_header
and src_file = {
  fname : string;
  fast : cunit;
}
and src_string = {
  sast : cunit;
}
and src_db_header = {
  dast : cunit;
}

let subst_cunit subst = function
  | Full (kn, cu) as orig ->
    let kn' = Mod_subst.subst_kn subst kn in
    let cu' = EC.map_compilation_unit (Rocq_elpi_HOAS.subst_cdata subst) cu in
    if kn == kn' && cu == cu' then orig else Full (kn', cu')
  | Signature (kn, cu) as orig ->
    let kn' = Mod_subst.subst_kn subst kn in
    if kn == kn' then orig  else Signature (kn', cu)

let subst_src subst = function
  | File ({ fname; fast } as f) ->
    let fast' = subst_cunit subst fast in
    if fast == fast' then File f else File { fname; fast = fast' }
  | EmbeddedString ({ sast } as s) ->
    let sast' = subst_cunit subst sast in
    if sast == sast' then EmbeddedString s else EmbeddedString { sast = sast' }
  | DatabaseBody n -> DatabaseBody n
  | DatabaseHeader ({ dast } as h) ->
    let dast' = subst_cunit subst dast in
    if dast == dast' then DatabaseHeader h else DatabaseHeader { dast = dast' }

let alpha = 65599
let combine_hash h1 h2 = h1 * alpha + h2

let hash_cunit = function
  | Full (kn,_) -> Names.KerName.hash kn
  | Signature (kn,_) -> Names.KerName.hash kn + 1
let compare_cunit a b =
  match a,b with
  | Full(kn1,_), Full(kn2,_) -> Names.KerName.compare kn1 kn2
  | Signature(kn1,_), Signature(kn2,_) -> Names.KerName.compare kn1 kn2
  | Full _, Signature _ -> -1
  | Signature _, Full _ -> +1

let hash_list f z l = List.fold_left (fun acc x -> combine_hash (f x) acc) z l

module Chunk = struct
  type t =
    | Base of {
      hash : int;
      base : cunit list;
    }
    | Snoc of {
      source_rev : cunit list;
      prev : t;
      hash : int
    }
  [@@deriving show, ord]
  let hash = function
    | Base { hash } -> hash
    | Snoc { hash } -> hash

  let snoc source_rev prev =
    let hash = (hash_list hash_cunit (hash prev) source_rev) in
    Snoc { hash; prev; source_rev }

  let rec base = function
    | Base { base } -> base
    | Snoc { prev } -> base prev

  let eq x y = compare x y == 0
end

module Code = struct
type ('base, 'db) t =
  | Base of {
    hash : int;
    base : 'base;
  }
  | Snoc of {
    source : cunit;
    prev : ('base, 'db) t;
    hash : int;
    cacheme: bool;
  }
  | Snoc_db of {
    chunks : 'db;
    prev : ('base, 'db) t;
    hash : int
  }
  [@@deriving show]
let hash = function
  | Base { hash } -> hash
  | Snoc { hash } -> hash
  | Snoc_db { hash } -> hash

let cache = function
  | Base _ -> true
  | Snoc { cacheme } -> cacheme
  | Snoc_db _ -> false

let snoc ?cache:ocache source prev =
let hash = combine_hash (hash prev) (hash_cunit source) in
  Snoc { hash; prev; source; cacheme = match ocache with Some cache -> cache | None -> cache prev }

let snoc_opt ?cache source prev =
  match prev with
  | Some prev -> snoc ?cache source prev
  | None -> Base { hash = (hash_cunit source); base = source }

let snoc_db f chunks prev =
  let hash = hash prev in
  let hash = combine_hash hash (f chunks) in
  Snoc_db { hash; prev; chunks }

let snoc_db_opt f chunks prev =
  match prev with
  | Some prev -> snoc_db f chunks prev
  | None -> assert false

let rec base = function
  | Base { base } -> base
  | Snoc { prev } | Snoc_db { prev } -> base prev

let eq (type a b) cu cb cdb : (a,b) t -> (a,b) t -> bool =
  let rec eq x y =
    x == y ||
    match x,y with
    | Base x, Base y -> cb x.base y.base
    | Snoc x, Snoc y -> cu x.source y.source && eq x.prev y.prev
    | Snoc_db x, Snoc_db y -> cdb x.chunks y.chunks && eq x.prev y.prev
    | _ -> false
  in eq

end

type db = {
  sources_rev : (cunit list, qualified_name) Code.t;
  units : Names.KNset.t;
  files : CString.Set.t;
  dbs : SLSet.t;
}

type nature = Command of { raw_args : bool } | Tactic | Program of { raw_args : bool }

type program = {
  sources_rev : (cunit, qualified_name) Code.t;
  files : CString.Set.t;
  units : Names.KNset.t;
  dbs : SLSet.t;
  empty : bool; (* it is empty, if it only contains default code *)
}

type from = Initialization | User

type db_initialization = {
  program : qualified_name;
  base : cunit list;
}

type 'a db_addition = {
  program : qualified_name;
  code : 'a;
  scope : Rocq_elpi_utils.clause_scope;
  vars : Names.Id.t list;
}

type 'a snippet =
  | DbInit of db_initialization
  | DbAdd of 'a db_addition

let scope_of_snippet : 'a snippet -> _ = function
  | DbInit _ -> Rocq_elpi_utils.SuperGlobal
  | DbAdd {scope} -> scope

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

(**********************************************************************)


module type Programs = sig

  open Elpi.API

  val debug_vars : Compile.StrSet.t ref
  val cc_flags : unit -> Compile.flags
  val unit_from_ast    : ?error_header:string -> elpi:Setup.elpi -> base:Compile.program -> loc:Loc.t -> Compile.scoped_program -> cunit
  val parse_goal       : elpi:Setup.elpi -> loc:Loc.t -> Ast.Loc.t -> string -> Ast.query

  val db_exists : qualified_name -> bool
  val program_exists : qualified_name -> bool
  val declare_db : program_name -> unit
  val declare_program : program_name -> nature -> unit
  val declare_file : program_name -> unit
  val get_nature : qualified_name -> nature

  val init_program : program_name -> loc:Loc.t -> (Ast.Loc.t * string) -> unit
  val init_command : program_name -> loc:Loc.t -> unit
  val init_tactic  : program_name -> loc:Loc.t -> unit
  val init_db      : program_name -> loc:Loc.t -> (Ast.Loc.t * string) -> unit
  val init_file    : program_name -> loc:Loc.t -> (Ast.Loc.t * string) -> unit

  val ast_of_elpifile : qualified_name -> Compile.scoped_program list

  type db_header
  val header_of_db : qualified_name -> db_header

  val accumulate_file_to_program     : loc:Loc.t -> program:qualified_name -> what:what -> file:string -> unit
  val accumulate_ast_to_program      : loc:Loc.t -> program:qualified_name -> what:what -> ast:Compile.scoped_program -> unit
  val accumulate_string_to_program   : loc:Loc.t -> program:qualified_name -> code:(Ast.Loc.t * string) -> unit
  val accumulate_plugin_to_program   : loc:Loc.t -> program:qualified_name -> plugin:Elpi.API.Setup.builtins -> unit
  val accumulate_db_to_program       : loc:Loc.t -> program:qualified_name -> db:qualified_name -> unit
  val accumulate_header_to_program   : loc:Loc.t -> program:qualified_name -> header:db_header -> unit

  val accumulate_file_to_db   : loc:Loc.t -> db:qualified_name -> what:what -> file:string -> scope:Rocq_elpi_utils.clause_scope -> unit
  val accumulate_ast_to_db    : loc:Loc.t -> db:qualified_name -> what:what -> ast:Compile.scoped_program -> scope:Rocq_elpi_utils.clause_scope -> unit
  val accumulate_string_to_db : loc:Loc.t -> db:qualified_name -> code:(Ast.Loc.t * string) -> scope:Rocq_elpi_utils.clause_scope -> unit
  val accumulate_string_to_db_with_secvars : loc:Loc.t -> db:qualified_name -> code:(Ast.Loc.t * string) -> secvars:Names.Id.t list -> scope:Rocq_elpi_utils.clause_scope -> unit
  val accumulate_units_to_db  : loc:Loc.t -> db:qualified_name -> units:cunit list -> secvars:Names.Id.t list -> scope:Rocq_elpi_utils.clause_scope -> unit
  val accumulate_db_to_db     : loc:Loc.t -> db:qualified_name -> source:qualified_name -> scope:Rocq_elpi_utils.clause_scope -> unit
  val accumulate_header_to_db : loc:Loc.t -> db:qualified_name -> header:db_header -> scope:Rocq_elpi_utils.clause_scope -> unit

  val load_command : loc:Loc.t -> string -> unit
  val load_tactic : loc:Loc.t -> string -> unit

  val ensure_initialized : unit -> Setup.elpi

  val code : ?even_if_empty:bool -> qualified_name -> (cunit, qualified_name) Code.t option

  val in_stage : string -> string
  val stage : Summary.Stage.t
  val db_inspect : qualified_name -> int

  val get_and_compile_existing_db : loc:Loc.t -> qualified_name -> Compile.program
  val get_and_compile : loc:Loc.t -> ?even_if_empty:bool -> qualified_name -> (Compile.program * bool) option


end


module type Stage = sig
  val stage : Summary.Stage.t
  val in_stage : string -> string
  val init : unit -> API.Setup.elpi
end

module SourcesStorage(S : Stage) = struct
  open S

  module Libobject = struct
    include Libobject
    let declare_named_object o = Libobject.declare_named_object { o with
      Libobject.object_stage = stage;
      Libobject.object_name = in_stage (o.Libobject.object_name)
    }
    let declare_object o = Libobject.declare_object { o with
      Libobject.object_stage = stage;
      Libobject.object_name = in_stage (o.Libobject.object_name)
    }
  end

  module Summary = struct
    include Summary
    let ref ?local ~name x = Summary.ref ~stage ?local ~name:(in_stage name) x
  end

  let program_name : nature SLMap.t ref =
    Summary.ref ~name:("elpi-programs") SLMap.empty
  let program_exists name = SLMap.mem name !program_name
  
  let get_nature p =
    try SLMap.find p !program_name
    with Not_found ->
      CErrors.user_err
        Pp.(str "No Elpi Program named " ++ pr_qualified_name p)

  let in_program_name : qualified_name * nature -> Libobject.obj =
    let open Libobject in
    declare_object @@ (superglobal_object_nodischarge "elpi-programs-names"
    ~cache:(fun (name,nature) ->
      program_name := SLMap.add name nature !program_name)
    ~subst:(Some (fun (_,x) -> x)))

  let declare_program name nature =
    let obj = in_program_name (name,nature) in
    Lib.add_leaf obj

  let db_name : SLSet.t ref = Summary.ref  ~name:("elpi-dbs") SLSet.empty
  let file_name : SLSet.t ref = Summary.ref  ~name:("elpi-files") SLSet.empty
  let db_exists name = SLSet.mem name !db_name
  let file_exists name = SLSet.mem name !file_name

  let in_db_name : qualified_name -> Libobject.obj =
    let open Libobject in
    declare_object @@
      (superglobal_object_nodischarge "elpi-db-names"
          ~cache:(fun name -> db_name := SLSet.add name !db_name)
          ~subst:(Some (fun (_,x) -> x)))

  let in_file_name : qualified_name -> Libobject.obj =
    let open Libobject in
    declare_object @@
      (superglobal_object_nodischarge "elpi-file-names"
          ~cache:(fun name -> file_name := SLSet.add name !file_name)
          ~subst:(Some (fun (_,x) -> x)))
        
  let declare_db program =
    ignore @@ Lib.add_leaf (in_db_name program)
  
  let declare_file program =
    ignore @@ Lib.add_leaf (in_file_name program)
          
  let declare_program (loc,qualid) nature =
    if program_exists qualid || db_exists qualid || file_exists qualid then
      CErrors.user_err Pp.(str "Program/Tactic/Db/File " ++ pr_qualified_name qualid ++ str " already exists")
    else
      declare_program qualid nature
      
  let declare_db (loc,qualid) =
    if program_exists qualid || db_exists qualid || file_exists qualid then
      CErrors.user_err Pp.(str "Program/Tactic/Db/File " ++ pr_qualified_name qualid ++ str " already exists")
    else
      declare_db qualid


  let declare_file (loc,qualid) =
    if program_exists qualid || db_exists qualid || file_exists qualid then
      CErrors.user_err Pp.(str "Program/Tactic/Db/File " ++ pr_qualified_name qualid ++ str " already exists")
    else
      declare_file qualid

let debug_vars = Summary.ref ~name:"elpi-debug" EC.StrSet.empty

let cc_flags () =
  { EC.default_flags with EC.defined_variables = !debug_vars }

let source_cache1 = Summary.ref ~local:true ~name:"elpi-units1" Names.KNmap.empty
let source_cache2 = Summary.ref ~local:true ~name:"elpi-units2" CString.Map.empty

let source_cache_lookup flags hash =
  let kn = CString.Map.find hash !source_cache2 in
  let u,cf = Names.KNmap.find kn !source_cache1 in
  if flags <> cf then raise Not_found (* TODO ERROR *)
  else kn, u

let last_kn = ref None

let in_source : Names.Id.t -> EC.compilation_unit * EC.flags -> Libobject.obj =
  let open Libobject in
  let cache ((_,kn), (u,cf)) =
    last_kn := Some kn;
    source_cache1 := Names.KNmap.add kn (u,cf) !source_cache1;
    source_cache2 := CString.Map.add (EC.compilation_unit_digest u) kn !source_cache2;
  in
  let import _ (_, s as o) = cache o in
  declare_named_object @@ { (default_object "ELPI-UNITS") with
    subst_function = (fun (_,o) -> o); (* Keep classification, subst unreachable *)
    load_function  = import;
    cache_function  = cache;
    open_function = my_filtered_open import;
    discharge_function = (fun o -> Some o);
    classify_function = (fun _ -> Keep);
  }
;;

let dig = ref 0

let intern x cc = 
  let id = Names.Id.of_string_soft
    @@ Printf.sprintf "%s:%s" (EC.compilation_unit_name x) (Digest.to_hex (EC.compilation_unit_digest x)) in
  Lib.add_leaf (in_source id (x,cc));
  let kn = Option.get !last_kn in
  let u,_ = Names.KNmap.find kn !source_cache1 in
  kn, u
  
let unit_from_ast ?error_header ~elpi ~flags ~base ~loc ast =
  try
    let kn, u = source_cache_lookup flags (EC.scoped_program_digest ast) in
    Full(kn,u)
  with Not_found ->
    handle_elpi_compiler_errors ~loc ?error_header (fun () ->
      let u = EC.unit ~elpi ~flags ~base ast in
      let kn, u = intern u flags in
      Full(kn,u))

let unit_signature_from_ast ~elpi ~flags ~base ~loc ast =
  try 
    let kn, u = source_cache_lookup (cc_flags ()) (EC.scoped_program_digest ast) in
    Signature (kn,EC.signature u)
  with Not_found ->
  handle_elpi_compiler_errors ~loc (fun () ->
    let u = EC.unit ~elpi ~flags ~base ast in
    let kn, u = intern u flags in
    Signature (kn,EC.signature u))
        
let unit_from_plugin ?error_header ~elpi ~base ~loc builtins ~flags : cunit =
  handle_elpi_compiler_errors ~loc (fun () ->
    let ast = EC.scope_builtins ~elpi builtins in
    let loc = Loc.initial Loc.ToplevelInput in
    unit_from_ast ~elpi ~flags ~base ~loc ast)

let assemble_unit ~loc base u =
  handle_elpi_compiler_errors ~loc (fun () ->
    match u with
    | Full(_, u) -> EC.extend ~base ~flags:(cc_flags ()) u
    | Signature(_, s) -> EC.extend_signature ~base ~flags:(cc_flags ()) s)
    
let assemble_units ~base ~loc units =
  List.fold_left (assemble_unit ~loc) base units

let extend_with_idependent_units = assemble_units
let extend_with_unit ~base ~loc u = assemble_units ~base ~loc [u]


let private__units_from_file ~elpi ~base ~loc x : cunit list =
  handle_elpi_compiler_errors ~loc (fun () ->
    let flags = cc_flags () in
    let ast = EP.program ~elpi ~file:x in
    let ast = EC.scope_ast ~elpi ast in
    let _, units_rev =
      List.fold_left (fun (base,acc) ast ->
        let u = unit_from_ast ~elpi ~flags ~base ~loc ast in
        let base = assemble_unit ~loc base u in
        base, u :: acc
        ) (base,[]) ast in
    List.rev units_rev) 

let private__units_from_string ~elpi ~base ~loc xloc x : cunit list =
  handle_elpi_compiler_errors ~loc (fun () ->
    let flags = cc_flags () in
    let ast = EP.program_from ~elpi ~loc:xloc ~digest:(Digest.string x) (Lexing.from_string x) in
    let ast = EC.scope_ast ~elpi ast in
    let _, units_rev =
      List.fold_left (fun (base,acc) ast ->
        let u = unit_from_ast ~elpi ~flags ~base ~loc ast in
        let base = assemble_unit ~loc base u in
        base, u :: acc
        ) (base,[]) ast in
    List.rev units_rev)

let parse_goal ~elpi ~loc tloc text =
  handle_elpi_compiler_errors ~loc (fun () ->
    EP.goal ~elpi ~loc:tloc ~text)

let program_src : program SLMap.t ref =
  Summary.ref ~name:("elpi-programs-src") SLMap.empty

let db_name_src : db SLMap.t ref =
  Summary.ref ~name:("elpi-db-src") SLMap.empty

let file_name_src : API.Compile.scoped_program list SLMap.t ref =
  Summary.ref ~name:("elpi-file-src") SLMap.empty

  (* Setup called *)
let elpi = Stdlib.ref None

let ensure_initialized =
  fun () ->
    match !elpi with
    | Some x -> x
    | None ->
        let e = S.init () in
        elpi := Some e;
        e

let get ?(fail_if_not_exists=false) p =
  let _elpi = ensure_initialized () in
  let nature = get_nature p in
  try
  let { sources_rev; files; units; dbs; empty } = SLMap.find p !program_src in
  files, units, dbs, Some nature, Some sources_rev, empty
  with Not_found ->
  if fail_if_not_exists then
    CErrors.user_err
      Pp.(str "No Elpi Program named " ++ pr_qualified_name p)
  else
    CString.Set.empty, Names.KNset.empty, SLSet.empty, None, None, true

  let append_to_prog from name src =
    let files, units, dbs, _, prog, empty = get name in
    let files, units, dbs, prog =
      match src with
      (* undup *)
      | File { fname; fast = u } when CString.Set.mem fname files || Names.KNset.mem (kn_of_cunit u) units -> files, units, dbs, prog
      | EmbeddedString { sast = u } when Names.KNset.mem (kn_of_cunit u) units -> files, units, dbs, prog
      | DatabaseHeader { dast = u } when Names.KNset.mem (kn_of_cunit u) units -> files, units, dbs, prog
      | DatabaseBody n  when SLSet.mem n dbs -> files, units, dbs, prog
      (* add *)
      | File { fname; fast = u } -> CString.Set.add fname files, Names.KNset.add (kn_of_cunit u) units, dbs, Some (Code.snoc_opt u prog)
      | EmbeddedString { sast = u } -> files, Names.KNset.add (kn_of_cunit u) units, dbs, Some (Code.snoc_opt u prog)
      | DatabaseHeader { dast = u } -> files, Names.KNset.add (kn_of_cunit u) units, dbs, Some (Code.snoc_opt u prog)
      | DatabaseBody n -> files, units, SLSet.add n dbs, Some (Code.snoc_db_opt Hashtbl.hash n prog)
      in
    let prog = Option.get prog in
    { files; units; dbs; sources_rev = prog; empty = empty && from = Initialization }
  
  let in_program : qualified_name * src * from -> Libobject.obj =
    let open Libobject in
    declare_object @@ superglobal_object_nodischarge "ELPI"
    ~cache:(fun (name,src_ast,from) ->
      program_src :=
        SLMap.add name (append_to_prog from name src_ast) !program_src)
    ~subst:(Some (fun (subst, (name, src_ast, from)) ->
      (name, subst_src subst src_ast, from)))
  
  
  let init_program name ~loc:_ ul =
    ul |> List.iter (fun u ->
      let obj = in_program (name, u, Initialization) in
      Lib.add_leaf obj)
  ;;
  
  let add_to_program name v =
    let obj = in_program (name, v, User) in
    Lib.add_leaf obj

  let get_db name =
    match SLMap.find_opt name !db_name_src with
    | Some {sources_rev; units; files; dbs} ->
      Some sources_rev, units, files, dbs, false
    | None ->
      None, Names.KNset.empty, CString.Set.empty, SLSet.empty, true

  let db_code_raw n : (cunit list, qualified_name) Code.t option =
    let sources,_,_,_,_ = get_db n in
    sources

  let code ?(even_if_empty=false) n : (cunit, qualified_name) Code.t option =
    let _,_,_,_,sources, empty = get n in
    if empty && not even_if_empty then None else sources

  let initialize_db name ~base =
    let (sources_rev, units, files, dbs, empty) = get_db name in
    if not empty then {sources_rev=Option.get sources_rev; units; files; dbs} else
    let units = List.fold_left (fun units u -> Names.KNset.add (kn_of_cunit u) units) units base in
    let sources_rev = Code.Base { hash = hash_list hash_cunit 0 base; base } in
    {sources_rev; units; files; dbs}

  let append_to_db name (src : src) =
    let (code, units, files, dbs, _) = get_db name in
    let code = Option.get code in
    let (files, units, dbs, code) =
      match src with
      | File { fname; fast = u } when CString.Set.mem fname files || Names.KNset.mem (kn_of_cunit u) units -> files, units, dbs, code
      | EmbeddedString { sast = u } when Names.KNset.mem (kn_of_cunit u) units -> files, units, dbs, code
      | DatabaseHeader { dast = u } when Names.KNset.mem (kn_of_cunit u) units -> files, units, dbs, code
      | DatabaseBody n when SLSet.mem n dbs -> files, units, dbs, code
      | File { fname; fast = u } -> CString.Set.add fname files, Names.KNset.add (kn_of_cunit u) units, dbs, Code.snoc u code
      | EmbeddedString { sast = u } -> files, Names.KNset.add (kn_of_cunit u) units, dbs, Code.snoc u code
      | DatabaseHeader { dast = u } -> files, Names.KNset.add (kn_of_cunit u) units, dbs, Code.snoc u code
      | DatabaseBody n ->
        assert (not (eq_qualified_name n name));
        files, units, SLSet.add n dbs, Code.snoc_db Hashtbl.hash n code
    in
    {sources_rev=code; units; files; dbs}
        
  let is_inside_current_library kn =
    Names.DirPath.equal
      (Lib.library_dp ())
       (Names.KerName.modpath kn |> Names.ModPath.dp)

  let in_db : Names.Id.t -> src snippet -> Libobject.obj =
    let open Libobject in
    let cache ((_,_kn),s) =
      match s with
      | DbInit {program=name; base} ->
        db_name_src := SLMap.add name (initialize_db name ~base) !db_name_src
      | DbAdd {program=name; code=p} ->
        db_name_src := SLMap.add name (append_to_db name p) !db_name_src in
    let load i ((_,kn),s as o) =
      let scope = scope_of_snippet s in
      if Int.equal i 1 ||
        (scope = Rocq_elpi_utils.Global && is_inside_current_library kn) ||
        scope = Rocq_elpi_utils.SuperGlobal then cache o in
    declare_named_object @@ { (default_object "ELPI-DB") with
      classify_function = (fun s ->
        let scope = scope_of_snippet s in
        match scope with
        | Rocq_elpi_utils.Local -> Dispose
        | Rocq_elpi_utils.Regular -> Substitute
        | Rocq_elpi_utils.Global -> Keep
        | Rocq_elpi_utils.SuperGlobal -> Keep);
      load_function  = load;
      cache_function  = cache;
      subst_function = (fun (subst, s) ->
        match s with
        | DbInit i -> DbInit { i with base = List.map (subst_cunit subst) i.base }
        | DbAdd a -> DbAdd { a with code = subst_src subst a.code });
      open_function = my_simple_open cache;
      discharge_function = (fun (s as o) ->
        let scope, vars =
          match s with
          | DbInit _ -> Rocq_elpi_utils.SuperGlobal, []
          | DbAdd a -> a.scope, a.vars
        in
        if scope = Rocq_elpi_utils.Local || (List.exists (fun x -> is_in_section (Names.GlobRef.VarRef x)) vars) then None
        else Some o);
    }
  
    let in_file : Names.Id.t -> (program_name * API.Compile.scoped_program list) -> Libobject.obj =
      let open Libobject in
      let cache ((_,kn),((_,name),p)) =
        file_name_src := SLMap.add name p !file_name_src in
      let load i ((_,kn),_ as o) = cache o in
      declare_named_object @@ { (default_object "ELPI-FILE") with
        classify_function = (fun _ -> Keep);
        load_function  = load;
        cache_function  = cache;
        subst_function = (fun (_,o) -> o);
        open_function = my_simple_open cache;
        discharge_function = (fun o -> Some o);
      }

  let accum = ref 0
  let add_to_db (s : src snippet) =
    ignore @@ Lib.add_leaf
      (in_db (Names.Id.of_string (incr accum; Printf.sprintf "_ELPI_%d" !accum)) s)

  let add_to_file program code =
    ignore @@ Lib.add_leaf
      (in_file (Names.Id.of_string (incr accum; Printf.sprintf "_ELPI_%d" !accum)) (program, code))
    

  let init_file qualid init =
    add_to_file qualid init
      
  let init_file p ~loc (sloc, s) =
  handle_elpi_compiler_errors ~loc begin fun () ->
    let elpi = ensure_initialized () in
    let ast = EP.program_from ~elpi ~loc:sloc ~digest:(Digest.string s) (Lexing.from_string s) in
    let asts = EC.scope_ast ~elpi ast in
     init_file p asts
  end


  type db_header = cunit list
  let header_of_db qulid : db_header =
    Code.base @@ (SLMap.find qulid !db_name_src).sources_rev

  let ast_of_elpifile qulid = SLMap.find qulid !file_name_src


  (* templates *)
  let lp_command_base = Summary.ref ~name:("elpi-lp-command") None
  let in_lp_command_src : src list -> Libobject.obj =
    let open Libobject in
    declare_object { (default_object "ELPI-LP-COMMAND") with
      load_function = (fun _ x -> lp_command_base := Some x);
      classify_function = (fun _ -> Keep);
    }
  let load_command ~loc s =
    let elpi = ensure_initialized () in
    let units = private__units_from_file ~elpi ~loc ~base:EC.(empty_base ~elpi) s in
    let base = List.map (fun u -> File { fname = name_of_cunit u; fast = u }) units in
    lp_command_base := Some base;
    Lib.add_leaf (in_lp_command_src base)
  let command_init () =
    match !lp_command_base with
    | None -> CErrors.user_err Pp.(str "Elpi CommandTemplate was not called")
    | Some ast -> ast

  let command_base_units () =
    command_init () |> List.map (function
    | File { fast } -> fast
    | EmbeddedString { sast } -> sast
    | _ -> assert false)

  let init_db qualid ~loc (sloc,s) =
    let elpi = ensure_initialized () in
    let base = EC.(empty_base ~elpi) in
    let cmd_base = command_base_units () in
    let base = extend_with_idependent_units ~base ~loc cmd_base in
    let units = private__units_from_string ~elpi ~base ~loc sloc s in
    add_to_db (DbInit { program = qualid; base = cmd_base @ units })
  
  let lp_tactic_ast = Summary.ref ~name:("elpi-lp-tactic") None
  let in_lp_tactic_ast : src list -> Libobject.obj =
    let open Libobject in
    declare_object { (default_object "ELPI-LP-TACTIC") with
      load_function = (fun _ x -> lp_tactic_ast := Some x);
      classify_function = (fun _ -> Keep);
    }
  let load_tactic ~loc s =
    let elpi = ensure_initialized () in
    let units = private__units_from_file ~elpi ~loc ~base:(EC.empty_base ~elpi) s in
    let base = List.map (fun u -> File { fname = name_of_cunit u; fast = u }) units in
    lp_tactic_ast := Some base;
    Lib.add_leaf (in_lp_tactic_ast base)
  let tactic_init () =
    match !lp_tactic_ast with
    | None -> CErrors.user_err Pp.(str "Elpi TacticTemplate was not called")
    | Some ast -> ast
  
  let init_program_units (loc,qualid) ~loc (init : src list) =
    if stage = Summary.Stage.Interp && Global.sections_are_opened () then
      CErrors.user_err Pp.(str "Program/Tactic/Db cannot be declared inside sections")
    else
      init_program qualid ~loc init

  let init_tactic n ~loc = init_program_units n loc (command_init () @ tactic_init ())
  let init_command n ~loc = init_program_units n loc (command_init ())

  let init_program p ~loc (sloc, s) =
    let elpi = ensure_initialized () in
    let base = EC.(empty_base ~elpi) in
    let units = private__units_from_string ~elpi ~base ~loc sloc s in
    init_program_units p ~loc (List.map (fun u -> EmbeddedString { sast = u }) units)

  
  let init_db (_,qualid) ~loc header =
    if stage = Summary.Stage.Interp && Global.sections_are_opened () then
      CErrors.user_err Pp.(str "Program/Tactic/Db cannot be declared inside sections")
    else if stage = Summary.Stage.Interp && match Global.current_modpath () with Names.ModPath.MPdot (Names.ModPath.MPfile _,_) -> true | _ -> false then
      CErrors.user_err Pp.(str "Program/Tactic/Db cannot be declared inside modules")
    else
    init_db qualid ~loc header
  ;;
    
  let accumulate_to_program p (v : src) =
    if not (program_exists p) then
      CErrors.user_err Pp.(str "No Elpi Program named " ++ pr_qualified_name p);
    add_to_program p v
  
  let accumulate_to_db' (a : src list db_addition) =
    if not (db_exists a.program) then
      CErrors.user_err Pp.(str "No Elpi Db " ++ pr_qualified_name a.program);
    let {program; vars; scope; code} = a in
    List.iter (fun code -> add_to_db (DbAdd {program; vars; scope; code})) code

  let accumulate_to_db p v ~vs ~scope =
    accumulate_to_db' { program = p; code = List.map (fun sast -> EmbeddedString {sast}) (List.rev v); vars = vs; scope }
  
  let in_stage = in_stage
  let stage = stage

  let db_inspect name =
    try Names.KNset.cardinal (SLMap.find name !db_name_src).units
  with Not_found -> -1
    
  let unit_from_ast ?error_header ~elpi ~base ~loc ast =
    unit_from_ast ?error_header ~elpi ~base ~loc ast ~flags:(cc_flags ())

let unit_signature_from_ast ~elpi ~base ~loc ast =
  unit_signature_from_ast ~elpi ~base ~loc ast ~flags:(cc_flags ())
  
let unit_from_plugin ?error_header ~elpi ~base ~loc builtins =
  unit_from_plugin ?error_header ~elpi ~base ~loc builtins ~flags:(cc_flags ())

module Visited = struct
  module Set = Names.KNset
  type t = {
    units : Set.t;
    dbs : SLSet.t;
  }
  let empty = { units = Set.empty; dbs = SLSet.empty }
  let add_unit u visited = { visited with units = Set.add (kn_of_cunit u) visited.units }
  let mem_unit u visited = Set.mem (kn_of_cunit u) visited.units
  let add_db n visited = { visited with dbs = SLSet.add n visited.dbs }
  let mem_db n visited = SLSet.mem n visited.dbs
end

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

type cache_stats = { lookups : int; hits : int }
let cache_stats = ref { lookups = 0; hits = 0 }

let find_with_stats k t =
  let { lookups; hits } = !cache_stats in
  try
    let rc = Int.Map.find k t in
    cache_stats := { lookups = lookups + 1; hits = hits + 1 };
    rc
  with Not_found ->
    cache_stats := { lookups = lookups + 1; hits };
    raise Not_found

let () = at_exit (fun () ->
  let { lookups; hits } = !cache_stats in
  Rocq_elpi_utils.debug Pp.(fun () ->
    str(Format.asprintf "Compiler cache: lookups=%d, hits=%d\n" lookups hits))
)

let lookup b h src r cmp pp =
  let h = combine_hash b h in
  let visited, p, src' = find_with_stats h !r in
  if cmp src src' then visited, p else
    let () = Format.eprintf "@[%a@]%!" pp src in
    let () = Format.eprintf "@[%a@]%!" pp src' in
    assert false

let cache b h visited prog src r =
  let h = combine_hash b h in
  r := Int.Map.add h (visited, prog, src) !r;
  visited, prog

let eq_cunits = List.equal eq_cunit
let pp_ignore _ _ = ()
let lookup_code b h src : Visited.t * EC.program = lookup b h src compiler_cache_code (Code.eq eq_cunit eq_cunit eq_qualified_name) (Code.pp pp_ignore pp_qualified_name)
let lookup_chunk b h src : Visited.t * EC.program = lookup b h src compiler_cache_chunk (Code.eq eq_cunit eq_cunits eq_qualified_name) (Code.pp pp_ignore pp_qualified_name)
let cache_code b h (visited : Visited.t) (prog : EC.program) src : Visited.t * EC.program = cache b h visited prog src compiler_cache_code
let cache_chunk b h (visited : Visited.t) (prog : EC.program) src : Visited.t * EC.program = cache b h visited prog src compiler_cache_chunk

let extend_unseen_unit ~loc ~base visited u =
  if Visited.mem_unit u visited then base, visited
  else extend_with_unit ~base ~loc u, Visited.add_unit u visited

let extend_unseen_units ~loc ~base visited units =
  List.fold_left (fun (base, visited) u ->
    extend_unseen_unit ~loc ~base visited u) (base, visited) units

let rec compile_code ~loc (src : (cunit, qualified_name) Code.t) : Visited.t * EC.program =
  let h = Code.hash src in
  try
    if not (Code.cache src) then raise Not_found;
    lookup_code 0 h src
  with Not_found ->
  match src with
  | Code.Base { base = u } ->
      let elpi = ensure_initialized () in
      let base = EC.empty_base ~elpi in
      let prog = extend_with_unit ~base ~loc u in
      cache_code 0 h (Visited.add_unit u Visited.empty) prog src
  | Code.Snoc { prev; source } ->
      let visited, base = compile_code ~loc prev in
      let base, visited = extend_unseen_unit ~loc ~base visited source in
      if Code.cache src then cache_code 0 h visited base src else visited, base
  | Code.Snoc_db { prev; chunks = db_name } ->
      let visited, base = compile_code ~loc prev in
      compile_db_name ~loc ~visited ~base db_name
and compile_db_name ~loc ~visited ~base db_name =
  if Visited.mem_db db_name visited then visited, base
  else
    match db_code_raw db_name with
    | None -> CErrors.user_err Pp.(str "Unknown Db " ++ pr_qualified_name db_name)
    | Some src ->
        let visited = Visited.add_db db_name visited in
        compile_db_code ~loc ~visited ~base src
and compile_db_code ~loc ~visited ~base (src : (cunit list, qualified_name) Code.t) : Visited.t * EC.program =
  match src with
  | Code.Base { base = units } ->
      let base, visited = extend_unseen_units ~loc ~base visited units in
      visited, base
  | Code.Snoc { prev; source } ->
      let visited, base = compile_db_code ~loc ~visited ~base prev in
      let base, visited = extend_unseen_unit ~loc ~base visited source in
      visited, base
  | Code.Snoc_db { prev; chunks = db_name } ->
      let visited, base = compile_db_code ~loc ~visited ~base prev in
      compile_db_name ~loc ~visited ~base db_name

let compile ~loc src =
  compile_code ~loc src |> snd

let compile_db ~loc src =
  let elpi = ensure_initialized () in
  let base = EC.empty_base ~elpi in
  compile_db_code ~loc ~visited:Visited.empty ~base src |> snd

let get_and_compile ~loc ?even_if_empty name : (EC.program * bool) option =
  let t = Unix.gettimeofday () in
  let res = code ?even_if_empty name |> Option.map (fun src ->
    let prog = compile ~loc src in
    let new_hash = Code.hash src in
    programs_tip := SLMap.add name new_hash !programs_tip;
    let raw_args =
      match get_nature name with
      | Command { raw_args } -> raw_args
      | Program { raw_args } -> raw_args
      | Tactic -> true in
      (prog, raw_args)) in
    Rocq_elpi_utils.elpitime (fun _ -> Pp.(str(Printf.sprintf "Elpi: get_and_compile %1.4f" (Unix.gettimeofday () -. t))));
    res

  let get_and_compile_existing_db ~loc name : EC.program =
    match db_code_raw name with
    | None -> err Pp.(str "Unknown Db " ++ pr_qualified_name name)
    | Some db -> compile_db ~loc db
    

  let get_and_compile_existing_program ~loc program : EC.program =
    match get_and_compile ~loc ~even_if_empty:true program with
    | None -> CErrors.user_err ~loc Pp.(str "Unknown program " ++ pr_qualified_name program)
    | Some (base, _) -> base

let asts_from_file ~elpi ~base ~loc x : EC.scoped_program list =
    handle_elpi_compiler_errors ~loc (fun () ->
      let ast = EP.program ~elpi ~file:x in
      EC.scope_ast ~elpi ast)

let asts_from_string ~loc (sloc,s) : EC.scoped_program list =
  handle_elpi_compiler_errors ~loc (fun () ->
    let elpi = ensure_initialized () in
    let digest = Digest.(string s) in
    let ast = EP.program_from ~elpi ~loc:sloc ~digest (Lexing.from_string s) in
    EC.scope_ast ~elpi ast)

  let accumulate_ast_to_X ~get_and_compile ~accumulate ~loc ~x ~what ast =
    handle_elpi_compiler_errors ~loc begin fun () -> 
      let elpi = ensure_initialized () in
      let base = get_and_compile ~loc x in
      let u = 
        match what with
        | Code -> unit_from_ast ~elpi ~base ~loc ast
        | SignatureOnly -> unit_signature_from_ast ~elpi ~base ~loc ast in
      accumulate x u
    end

  let accumulate_ast_to_program ~loc ~program ~what ~ast =
    accumulate_ast_to_X ~loc ~x:program ~what ast
      ~get_and_compile:get_and_compile_existing_program
      ~accumulate:(fun n u -> accumulate_to_program n (EmbeddedString { sast = u }))

  let accumulate_ast_to_db ~loc ~db ~what ~ast ~scope =
    accumulate_ast_to_X ~loc ~x:db ~what ast
      ~get_and_compile:get_and_compile_existing_db
      ~accumulate:(fun n u -> 
        accumulate_to_db ~scope ~vs:[] n [u])

  let accumulate_file_to_X ~get_and_compile ~accumulate ~loc ~x ~what ~file =
    handle_elpi_compiler_errors ~loc begin fun () -> 
      let elpi = ensure_initialized () in
      let base = get_and_compile ~loc x in
      let asts = asts_from_file ~loc ~elpi ~base file in
      List.iter (accumulate_ast_to_X ~get_and_compile ~accumulate ~loc ~x ~what) asts
    end

  let accumulate_file_to_program ~loc ~program ~what ~file =
    accumulate_file_to_X ~loc ~x:program ~what ~file
      ~get_and_compile:get_and_compile_existing_program
      ~accumulate:(fun n u -> accumulate_to_program n (File { fname = name_of_cunit u; fast = u }))

  let accumulate_file_to_db ~loc ~db ~what ~file ~scope =
    handle_elpi_compiler_errors ~loc begin fun () ->
      let elpi = ensure_initialized () in
      let base = get_and_compile_existing_db ~loc db in
      let asts = asts_from_file ~loc ~elpi ~base file in
      List.iteri (fun i ast ->
        let base = get_and_compile_existing_db ~loc db in
        let u =
          match what with
          | Code -> unit_from_ast ~elpi ~base ~loc ast
          | SignatureOnly -> unit_signature_from_ast ~elpi ~base ~loc ast in
        accumulate_to_db' { program = db; vars = []; scope;
          code = [File { fname = Printf.sprintf "%s:%d" file i; fast = u }] }) asts
    end

  let accumulate_string_to_program ~loc ~program ~code =
    asts_from_string ~loc code
    |> List.iter (fun ast -> accumulate_ast_to_program ~loc ~program ~what:Code ~ast)

  let accumulate_string_to_db_with_secvars ~loc ~db ~code ~secvars ~scope =
    asts_from_string ~loc code
    |> List.iter (fun ast ->
      accumulate_ast_to_X ~loc ~x:db ~what:Code ast
        ~get_and_compile:get_and_compile_existing_db
        ~accumulate:(fun n u -> accumulate_to_db ~scope ~vs:secvars n [u]))

  let accumulate_string_to_db ~loc ~db ~code ~scope =
    accumulate_string_to_db_with_secvars ~loc ~db ~code ~secvars:[] ~scope

  let accumulate_plugin_to_program ~loc ~program ~plugin =
    handle_elpi_compiler_errors ~loc begin fun () -> 
      let elpi = ensure_initialized () in
      let base = get_and_compile_existing_program ~loc program in
      let u = unit_from_plugin ~loc ~elpi ~base plugin in
      accumulate_to_program program (File { fname = name_of_cunit u; fast = u })
    end

 let accumulate_db_to_program ~loc ~program ~db =
    handle_elpi_compiler_errors ~loc begin fun () ->
      if db_exists db then
        let header = header_of_db db |> List.map (fun dast -> DatabaseHeader { dast }) in
        (header @ [DatabaseBody db]) |> List.iter (fun src ->
          accumulate_to_program program src)
      else
        CErrors.user_err Pp.(str "Db " ++ pr_qualified_name db ++ str" not found")
    end

  let accumulate_db_to_db ~loc ~db ~source ~scope =
    handle_elpi_compiler_errors ~loc begin fun () ->
      if db_exists source then
        let header = header_of_db source |> List.map (fun dast -> DatabaseHeader { dast }) in
        accumulate_to_db' { program = db; code = header @ [DatabaseBody source]; vars = []; scope }
      else
        CErrors.user_err Pp.(str "Db " ++ pr_qualified_name source ++ str" not found")
    end


  let accumulate_units_to_db ~loc ~db ~units ~secvars ~scope =
    handle_elpi_compiler_errors ~loc begin fun () -> 
      accumulate_to_db db ~scope ~vs:secvars units
    end


  let accumulate_header_to_program ~loc ~program ~header =
    handle_elpi_compiler_errors ~loc begin fun () ->
      List.iter (fun u -> accumulate_to_program program (File { fname = name_of_cunit u; fast = u })) header
    end

  let accumulate_header_to_db ~loc ~db ~header ~scope =
    handle_elpi_compiler_errors ~loc begin fun () ->
      accumulate_to_db db ~scope ~vs:[] header
    end

(* This block is to check early compilation will succeed *)
let check ~loc ~program = handle_elpi_compiler_errors ~loc (fun () -> get_and_compile_existing_program ~loc program |> ignore)
let check_db ~loc ~db = handle_elpi_compiler_errors ~loc (fun () -> get_and_compile_existing_db ~loc db |> ignore)
let accumulate_file_to_program ~loc ~program ~what ~file = accumulate_file_to_program ~loc ~program ~what ~file; check ~loc ~program
let accumulate_ast_to_program ~loc ~program ~what ~ast = accumulate_ast_to_program ~loc ~program ~what ~ast; check ~loc ~program
let accumulate_string_to_program ~loc ~program ~code = accumulate_string_to_program ~loc ~program ~code; check ~loc ~program
let accumulate_plugin_to_program ~loc ~program ~plugin = accumulate_plugin_to_program ~loc ~program ~plugin; check ~loc ~program
let accumulate_db_to_program ~loc ~program ~db = accumulate_db_to_program ~loc ~program ~db; check ~loc ~program
let accumulate_header_to_program ~loc ~program ~header = accumulate_header_to_program ~loc ~program ~header; check ~loc ~program
let accumulate_file_to_db ~loc ~db ~what ~file ~scope = accumulate_file_to_db ~loc ~db ~what ~file ~scope; check_db ~loc ~db
let accumulate_ast_to_db ~loc ~db ~what ~ast ~scope = accumulate_ast_to_db ~loc ~db ~what ~ast ~scope; check_db ~loc ~db
let accumulate_string_to_db ~loc ~db ~code ~scope = accumulate_string_to_db ~loc ~db ~code ~scope; check_db ~loc ~db
let accumulate_string_to_db_with_secvars ~loc ~db ~code ~secvars ~scope = accumulate_string_to_db_with_secvars ~loc ~db ~code ~secvars ~scope; check_db ~loc ~db
let accumulate_units_to_db ~loc ~db ~units ~secvars ~scope = accumulate_units_to_db ~loc ~db ~units ~secvars ~scope; check_db ~loc ~db
let accumulate_db_to_db ~loc ~db ~source ~scope = accumulate_db_to_db ~loc ~db ~source ~scope; check_db ~loc ~db
let accumulate_header_to_db ~loc ~db ~header ~scope = accumulate_header_to_db ~loc ~db ~header ~scope; check_db ~loc ~db

let init_program name ~loc sources = init_program name ~loc sources; check ~loc ~program:(snd name)

end

(***********************************************************************)
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

let coq_interp_builtins =
  API.BuiltIn.declare
    ~file_name:"coq-builtin.elpi"
    begin
      Rocq_elpi_builtins.coq_header_builtins @
      Rocq_elpi_builtins.coq_misc_builtins @
      Rocq_elpi_builtins.coq_locate_builtins @
      Rocq_elpi_builtins.coq_rest_builtins
    end

let coq_synterp_builtins =
  API.BuiltIn.declare
    ~file_name:"coq-builtin-synterp.elpi"
    begin
      [
        API.BuiltIn.LPCode {|
kind implicit_kind type.
kind field-attribute type.
kind upoly-decl type.
kind upoly-decl-cumul type.

        |}
      ] @
      Rocq_elpi_builtins.coq_misc_builtins @
      Rocq_elpi_builtins_synterp.coq_synterp_builtins
    end

let resolve_file_path ~must_exist ~allow_absolute ~only_elpi file =
  (* Handle absolute paths, as bound by "Extra Dependency". *)
  if allow_absolute && not (Filename.is_relative file) then
    if not must_exist || Sys.file_exists file then file else
    let msg = "The referenced absolute path " ^ file ^ " does not exist." in
    CErrors.user_err (Pp.str msg)
  else
  (* Split filename into a logical path, and a remaining relative path. *)
  let (logpath, relpath) =
    (* Remove "coq://" prefix for backward compatibility. *)
    let path =
      if String.length file >= 6 && String.sub file 0 6 = "coq://" then
        String.sub file 6 (String.length file - 6)
      else file
    in
    (* Remove ".elpi" extension if applicable. *)
    let path =
      if only_elpi && Filename.check_suffix path ".elpi" then
        String.sub path 0 (String.length path - 5)
      else path
    in
    match String.split_on_char '/' path with
    | logpath :: ((_ :: _) as relpath) ->
        let logpath =
          let logpath = String.split_on_char '.' logpath in
          let logpath = List.rev_map Names.Id.of_string logpath in
          Names.DirPath.make logpath
        in
        let relpath =
          let relpath = String.concat "/" relpath in
          if only_elpi then relpath ^ ".elpi" else relpath
        in
        (logpath, relpath)
    | _ ->
        let msg =
          "File reference " ^ file ^ " is ill-formed, and cannot be resolved."
        in
        CErrors.user_err (Pp.str msg)
  in
  (* Lookup the directory path in Coq's state. *)
  let mk_file_path p = Filename.concat (Loadpath.physical p) relpath in
  let loadpath = Loadpath.find_with_logical_path logpath in
  let loadpath =
    if not must_exist then loadpath
    else List.filter (fun p -> Sys.file_exists (mk_file_path p)) loadpath in
  let loadpath =
    match loadpath with
    | p :: [] -> p
    | []      ->
        let msg =
          "No loadpath found with logical name " ^
          Names.DirPath.to_string logpath ^
          ", cannot resolve file reference " ^ file ^ "."
        in
        CErrors.user_err (Pp.str msg)
    | ps      ->
        let msg =
          "Multiple loadpaths found with logical name " ^
          Names.DirPath.to_string logpath ^
          ", while resolving file reference " ^ file ^ ":\n" ^
          String.concat "\n" (List.map (fun lp ->
            Printf.sprintf "- %s -> %s"
              (Names.DirPath.to_string (Loadpath.logical lp))
              (Loadpath.physical lp)
          ) ps)
        in
        CErrors.user_err (Pp.str msg)
  in
  (* Assemble the file path. *)
  let resolved = mk_file_path loadpath in
  if not must_exist || Sys.file_exists resolved then resolved else
  let msg =
    "File reference " ^ file ^ " was resolved to " ^ resolved ^
    " but the file does not exist."
  in
  CErrors.user_err (Pp.str msg)

let file_resolver ?cwd:_ ~unit:file () =
  resolve_file_path ~must_exist:true ~allow_absolute:true ~only_elpi:true file

(***********************************************************************)

let versions =
  let open API.Setup.StrMap in
  empty
  |> add "coq-elpi" (API.Utils.version_parser ~what:"coq-elpi" "%%VERSION_NUM%%")
  |> add "rocq-elpi" (API.Utils.version_parser ~what:"rocq-elpi" "%%VERSION_NUM%%")
  |> add "coq" (API.Utils.version_parser ~what:"coq" Coq_config.version)
  |> add "rocq" (API.Utils.version_parser ~what:"rocq" Coq_config.version)
          
module Synterp : Programs = struct
  module S = struct
    let stage = Summary.Stage.Synterp
    let in_stage x = x ^ "-synterp"
    let init () =
      API.Setup.init ~versions
        ~state:synterp_state ~hoas:synterp_hoas
        ~quotations:synterp_quotations ~builtins:[elpi_builtins;coq_synterp_builtins] ~file_resolver ()
  end
  include SourcesStorage(S)

  let () = Rocq_elpi_builtins_synterp.set_accumulate_to_db_synterp (fun ~loc clauses_to_add ->
    let elpi = ensure_initialized () in
    let clauses_to_add = clauses_to_add |> group_clauses |>
      List.map (fun (dbname,asts,vs,scope) ->
        let base = get_and_compile_existing_db ~loc dbname in
        let scoped_asts = List.concat (List.map (EC.scope_ast ~elpi) asts) in
        let units = List.map (fun x ->
            unit_from_ast ~error_header:(Format.asprintf "accumulating clause to %s" (String.concat "." dbname)) ~elpi ~base ~loc x) scoped_asts in
        dbname,units,vs,scope) in
    clauses_to_add |> List.iter (fun (dbname,units,vs,scope) ->
      accumulate_to_db dbname units ~vs ~scope))
  
end
module Interp : Programs = struct
  include SourcesStorage(struct
    let stage = Summary.Stage.Interp
    let in_stage x = x ^ "-interp"
    let init () =
      API.Setup.init ~versions
        ~state:interp_state ~hoas:interp_hoas
        ~quotations:interp_quotations ~builtins:[elpi_builtins;coq_interp_builtins] ~file_resolver ()
  end)

let () = Rocq_elpi_builtins.set_accumulate_to_db_interp (fun ~loc clauses_to_add ->
  let elpi = ensure_initialized () in
  let clauses_to_add = clauses_to_add |> group_clauses |>
    List.map (fun (dbname,asts,vs,scope) ->
      let base = get_and_compile_existing_db ~loc dbname in
      let scoped_asts = List.concat (List.map (EC.scope_ast ~elpi) asts) in
      let units = List.map (fun x -> unit_from_ast ~error_header:(Format.asprintf "accumulating clause to %s" (String.concat "." dbname)) ~elpi ~base ~loc x) scoped_asts in
      dbname,units,vs,scope) in
  clauses_to_add |> List.iter (fun (dbname,units,vs,scope) ->
    accumulate_to_db dbname units ~vs ~scope))
  
let () = Rocq_elpi_builtins.set_accumulate_text_to_db_interp (fun ~loc n txt scope ->
      let elpi = ensure_initialized () in
      let base = get_and_compile_existing_db ~loc n in
      let u = private__units_from_string ~elpi ~base ~loc (of_coq_loc loc) txt in
  accumulate_to_db n u ~vs:[] ~scope)

end

let document_builtins () =
  API.BuiltIn.document_file coq_interp_builtins;
  API.BuiltIn.document_file coq_synterp_builtins;
  API.BuiltIn.document_file ~header:"% Generated file, do not edit" elpi_builtins

