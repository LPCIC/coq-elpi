(* rocq-elpi: Coq terms as the object language of elpi                       *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
module EC = API.Compile
module EP = API.Parse

open Rocq_elpi_utils
type program_name = Loc.t * qualified_name
type cunit = Full of Names.KerName.t * EC.compilation_unit | Signature of EC.compilation_unit_signature

let pp_cunit fmt = function | Full (kn,_) -> Format.fprintf fmt "%s" Names.KerName.(debug_to_string kn) | Signature _ -> Format.fprintf fmt "sig"
let eq_cunit x y =
  match x,y with
  | Full(k1,_), Full(k2,_) -> Names.KerName.equal k1 k2
  | Signature s1, Signature s2 -> Hashtbl.hash s1 == Hashtbl.hash s2 (* BUG *)
  | _ -> false

[%%if coq = "8.20" || coq = "9.0"]
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

let alpha = 65599
let combine_hash h1 h2 = h1 * alpha + h2

let hash_cunit = function | Full (kn,_) -> Names.KerName.hash kn | Signature s -> Hashtbl.hash s (* TODO *)
let compare_cunit a b =
  match a,b with
  | Full(kn1,_), Full(kn2,_) -> Names.KerName.compare kn1 kn2
  | Signature s1, Signature s2 -> if Hashtbl.hash s1 == Hashtbl.hash s2 then 0 else -1 (* BUG *)
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
  base_sig : cunit;
  base: cunit;
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
  val debug_vars : API.Compile.StrSet.t ref
  val cc_flags : unit -> API.Compile.flags
  val unit_from_file   : elpi:API.Setup.elpi -> base:API.Compile.program -> loc:Loc.t -> string -> cunit
  val unit_signature_from_file   : elpi:API.Setup.elpi -> base:API.Compile.program -> loc:Loc.t -> string -> cunit
  val unit_from_string : elpi:API.Setup.elpi -> base:API.Compile.program -> loc:Loc.t -> API.Ast.Loc.t -> string -> cunit
  val ast_from_string : elpi:API.Setup.elpi -> loc:Loc.t -> API.Ast.Loc.t -> string -> Digest.t * API.Compile.scoped_program
  val unit_from_ast    : ?error_header:string -> elpi:API.Setup.elpi -> base:API.Compile.program -> loc:Loc.t -> string option -> API.Compile.scoped_program -> cunit
  val unit_signature_from_ast    : elpi:API.Setup.elpi -> base:API.Compile.program -> loc:Loc.t -> string option -> API.Compile.scoped_program -> cunit
  val extend_w_units : base:API.Compile.program -> loc:Loc.t -> cunit list -> API.Compile.program
  val parse_goal : elpi:API.Setup.elpi -> loc:Loc.t -> API.Ast.Loc.t -> string -> API.Ast.query

  val db_exists : qualified_name -> bool
  val program_exists : qualified_name -> bool
  val declare_db : program_name -> unit
  val declare_program : program_name -> nature -> unit
  val declare_file : program_name -> unit
  val get_nature : qualified_name -> nature

  val init_program : program_name -> loc:Loc.t -> src list -> unit
  val init_db : program_name -> loc:Loc.t -> (API.Ast.Loc.t * string) -> unit
  val init_file : program_name -> Digest.t * API.Compile.scoped_program -> unit
  val header_of_db : qualified_name -> cunit list
  val ast_of_file : qualified_name -> Digest.t * API.Compile.scoped_program


  val accumulate : loc:Loc.t -> qualified_name -> src list -> unit
  val accumulate_to_db : loc:Loc.t -> qualified_name -> cunit list -> Names.Id.t list -> scope:Rocq_elpi_utils.clause_scope -> unit
  val accumulate_to_db' : loc:Loc.t -> src list db_addition -> unit
  val load_command : loc:Loc.t -> string -> unit
  val load_tactic : loc:Loc.t -> string -> unit

  val ensure_initialized : unit -> API.Setup.elpi

  val tactic_init : unit -> src
  val command_init : unit -> src

  val code : ?even_if_empty:bool -> qualified_name -> (cunit, qualified_name) Code.t option

  val in_stage : string -> string
  val stage : Summary.Stage.t

  val db_inspect : qualified_name -> int

  val get_and_compile_existing_db : loc:Loc.t -> qualified_name -> EC.program
  val get_and_compile : loc:Loc.t -> ?even_if_empty:bool -> qualified_name -> (EC.program * bool) option

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
    ~subst:(Some (fun _ -> CErrors.user_err Pp.(str"elpi: No functors yet"))))

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
          ~subst:(Some (fun _ -> CErrors.user_err Pp.(str"elpi: No functors yet"))))

  let in_file_name : qualified_name -> Libobject.obj =
    let open Libobject in
    declare_object @@
      (superglobal_object_nodischarge "elpi-file-names"
          ~cache:(fun name -> file_name := SLSet.add name !file_name)
          ~subst:(Some (fun _ -> CErrors.user_err Pp.(str"elpi: No functors yet"))))
        
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
    open_function = my_filtered_open import;
    discharge_function = (fun o -> Some o);
    classify_function = (fun _ -> Keep);
  }
;;

let dig = ref 0

let intern (hash,_,_ as x) = 
  let id = Names.Id.of_string_soft
    (match hash with Some x -> x | None -> incr dig; string_of_int !dig) in
  Lib.add_leaf (in_source id x);
  let kn = Option.get !last_kn in
  let u,_ = Names.KNmap.find kn !source_cache1 in
  kn, u

let intern_unit u =
  let kn, u = intern u in
  Full(kn,u)
let intern_unit_signature u =
  let _kn, u = intern u in
  Signature (EC.signature u)
  
(* Source files can be large, and loaded multiple times since many entry point
   can be implemented in the same file. We share (in memory) the parsed file. *)
let unit_from_ast ?error_header ~elpi ~flags h ~base ~loc ast =
  handle_elpi_compiler_errors ~loc ?error_header (fun () ->
    let u = EC.unit ~elpi ~flags ~base ast in
    intern_unit (h,u,flags))

let unit_signature_from_ast ~elpi ~flags h ~base ~loc ast =
  handle_elpi_compiler_errors ~loc (fun () ->
    let u = EC.unit ~elpi ~flags ~base ast in
    intern_unit_signature (h,u,flags))
        
let unit_from_file ~elpi ~base ~loc x : cunit =
  let flags = cc_flags () in
  let hash = Digest.(to_hex @@ file (EP.resolve_file ~elpi ~unit:x ())) in
  (* Feedback.msg_debug Pp.(str "unit_from_file: " ++ str x ++ str "; hash = " ++ str hash); *)
  try
    let kn, u = source_cache_lookup flags hash in
    Full (kn,u)
  with Not_found ->
    handle_elpi_compiler_errors ~loc (fun () ->
      let ast = EP.program ~elpi ~files:[x] in
      let ast = EC.scope ~elpi ast in
      let loc = Loc.initial Loc.ToplevelInput in
      unit_from_ast ~elpi ~flags (Some hash) ~base ~loc ast)

let unit_signature_from_file ~elpi ~base ~loc x : cunit =
  let flags = cc_flags () in
  let hash = Digest.(to_hex @@ file (EP.resolve_file ~elpi ~unit:x ())) in
  try
    let kn, u = source_cache_lookup flags hash in
    Signature (EC.signature u)
  with Not_found ->
    handle_elpi_compiler_errors ~loc (fun () ->
      let ast = EP.program ~elpi ~files:[x] in
      let ast = EC.scope ~elpi ast in
      let loc = Loc.initial Loc.ToplevelInput in
      unit_signature_from_ast ~elpi ~flags (Some hash) ~base ~loc ast)
      

let unit_from_string ~elpi ~base ~loc xloc x : cunit =
  let flags = cc_flags () in
  let hash = Digest.(to_hex @@ string x) in
  (* TODO: ERROR SAME HASH *)
  handle_elpi_compiler_errors ~loc (fun () ->
    let ast = EP.program_from ~elpi ~loc:xloc (Lexing.from_string x) in
    let ast = EC.scope ~elpi ast in
    unit_from_ast ~elpi ~flags (Some hash) ~base ~loc ast)

let ast_from_string ~elpi ~loc xloc x : string * API.Compile.scoped_program =
  let hash = Digest.(to_hex @@ string x) in
  handle_elpi_compiler_errors ~loc (fun () ->
    hash, EP.program_from ~elpi ~loc:xloc (Lexing.from_string x) |> EC.scope ~elpi)

let parse_goal ~elpi ~loc tloc text =
  handle_elpi_compiler_errors ~loc (fun () ->
    EP.goal ~elpi ~loc:tloc ~text)

let assemble_units ~base ~loc units =
  List.fold_left (fun base u ->
    handle_elpi_compiler_errors ~loc (fun () ->
      match u with
      | Full(_, u) -> EC.extend ~base ~flags:(cc_flags ()) u
      | Signature s -> EC.extend_signature ~base ~flags:(cc_flags ()) s))
    base units
let extend_w_units = assemble_units
let program_src : program SLMap.t ref =
  Summary.ref ~name:("elpi-programs-src") SLMap.empty

let db_name_src : db SLMap.t ref =
  Summary.ref ~name:("elpi-db-src") SLMap.empty

let file_name_src : (Digest.t * API.Compile.scoped_program) SLMap.t ref =
  Summary.ref ~name:("elpi-file-src") SLMap.empty

  (* Setup called *)
let elpi = Stdlib.ref None

let ensure_initialized =
  let init = lazy (let e = S.init () in elpi := Some e; e) in
  fun () -> Lazy.force init

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
      | File { fname; fast = Full (kn,_) } when CString.Set.mem fname files || Names.KNset.mem kn units -> files, units, dbs, prog
      | EmbeddedString { sast = Full(kn,_) } when Names.KNset.mem kn units -> files, units, dbs, prog
      | DatabaseHeader { dast = Full(kn,_) } when Names.KNset.mem kn units -> files, units, dbs, prog
      | DatabaseBody n  when SLSet.mem n dbs -> files, units, dbs, prog
      (* add *)
      | File { fname; fast = Full (kn,_) as u } -> CString.Set.add fname files, (Names.KNset.add kn units), dbs, Some (Code.snoc_opt u prog)
      | EmbeddedString { sast = Full (kn,_) as u } -> files, (Names.KNset.add kn units), dbs, Some (Code.snoc_opt u prog)
      | DatabaseHeader { dast = Full(kn,_) as u } ->  files, (Names.KNset.add kn units), dbs, Some (Code.snoc_opt u prog)
      | DatabaseBody n ->  files, units, SLSet.add n dbs, Some (Code.snoc_db_opt Hashtbl.hash n prog)
      | File { fast = Signature _ as u } -> files, units, dbs, Some (Code.snoc_opt u prog)
      | DatabaseHeader { dast = Signature _ as u } ->
         files, units, dbs, Some (Code.snoc_opt u prog)
      | EmbeddedString _ -> assert false (* TODO *)
      in
    let prog = Option.get prog in
    { files; units; dbs; sources_rev = prog; empty = empty && from = Initialization }
  

  let in_program : qualified_name * src * from -> Libobject.obj =
    let open Libobject in
    declare_object @@ superglobal_object_nodischarge "ELPI"
    ~cache:(fun (name,src_ast,from) ->
      program_src :=
        SLMap.add name (append_to_prog from name src_ast) !program_src)
    ~subst:(Some (fun _ -> CErrors.user_err Pp.(str"elpi: No functors yet")))
  
  
  let init_program name ~loc:_ ul =
    ul |> List.iter (fun u ->
      let obj = in_program (name, u, Initialization) in
      Lib.add_leaf obj)
  ;;
  
  let add_to_program name v =
    let obj = in_program (name, v, User) in
    Lib.add_leaf obj

  let transplant_db_code (type a b) ~f_db_base ~db_code : base:(_) -> (a, qualified_name) Code.t -> (b, qualified_name) Code.t =
    let rec go ~base c =
      match c with
      | Code.Base {base=headers} as orig -> f_db_base ~base ~orig headers
      | Code.Snoc { prev; source } ->
        Code.snoc ~cache:false source (go ~base prev)
      | Code.Snoc_db { prev; chunks=db } ->
        match db_code db with
        | None -> go ~base prev
        | Some code ->
        let base = go ~base prev in
        (* Feedback.msg_debug Pp.(str "Transplanting code for db: " ++ pr_qualified_name db); *)
        go ~base code
    in go

  let get_db name =
    match SLMap.find_opt name !db_name_src with
    | Some {sources_rev; units; files; dbs} ->
      (Some sources_rev, units, files, dbs, false)
    | None ->
      None, Names.KNset.empty, CString.Set.empty, SLSet.empty, true

  let db_code_raw n : (cunit list, qualified_name) Code.t option =
    (* Feedback.msg_debug Pp.(str "Getting raw code for db: " ++ pr_qualified_name n); *)
    let sources,_,_,_, _empty = get_db n in
    sources

  let code ?(even_if_empty=false) n : (_, qualified_name) Code.t option =
    let _,_,_,_,sources, empty = get n in
    if empty && not even_if_empty then None else
      sources


  let initialize_db name kname ~base_sig ~base =
    let (sources_rev, units, files, dbs, empty) = get_db name in
    if not empty then {sources_rev=Option.get sources_rev; units; files; dbs} else
    let units = Names.KNset.add kname units in
    let sources = [base_sig; base] in
    let sources_rev = Code.Base { hash = hash_list hash_cunit 0 sources; base = sources } in
    {sources_rev; units; files; dbs}

  let append_to_db name kname (src : src) =
    let (code, units, files, dbs, _) = get_db name in
    if Names.KNset.mem kname units then {sources_rev=Option.get code; units; files; dbs}
    else
      let code = Option.get code in
      let (files, units, dbs, code) =
        match src with
        | File { fname; fast = Full (kn,_) } when CString.Set.mem fname files || Names.KNset.mem kn units -> files, units, dbs, code
        | EmbeddedString { sast = Full(kn,_) } when Names.KNset.mem kn units -> files, units, dbs, code
        | DatabaseHeader { dast = Full(kn,_) } when Names.KNset.mem kn units -> files, units, dbs, code
        | DatabaseBody n  when SLSet.mem n dbs -> files, units, dbs, code
        (* add *)
        | File { fname; fast = Full (kn,_) as u } -> CString.Set.add fname files, (Names.KNset.add kn units), dbs, (Code.snoc u code)
        | EmbeddedString { sast = Full (kn,_) as u } -> files, (Names.KNset.add kn units), dbs, (Code.snoc u code)
        | DatabaseHeader { dast = Full(kn,_) as u } -> files, (Names.KNset.add kn units), dbs, (Code.snoc u code)
        | DatabaseBody n ->
          assert (not (eq_qualified_name n name));
          (files, units, SLSet.add n dbs, (Code.snoc_db Hashtbl.hash n code))
        | File { fast = Signature _ as u } -> files, units, dbs, (Code.snoc u code)
        | DatabaseHeader { dast = Signature _ as u } ->
          files, units, dbs, (Code.snoc u code)
        | EmbeddedString _ -> assert false (* TODO *)
      in
      {sources_rev=code; units; files; dbs}

  let is_inside_current_library kn =
    Names.DirPath.equal
      (Lib.library_dp ())
       (Names.KerName.modpath kn |> Names.ModPath.dp)

  let in_db : Names.Id.t -> src snippet -> Libobject.obj =
    let open Libobject in
    let cache ((_,kn), s) =
      match s with
      | DbAdd {program=name;code=p} ->
        db_name_src := SLMap.add name (append_to_db name kn p) !db_name_src
      | DbInit {program=name; base; base_sig} ->
        db_name_src := SLMap.add name (initialize_db name kn ~base ~base_sig) !db_name_src
    in
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
      subst_function = (fun (_,o) -> o);
      open_function = my_simple_open cache;
      discharge_function = (fun (s as o) ->
        let scope, program, vars =
          match s with
          | DbInit i -> Rocq_elpi_utils.SuperGlobal, i.program, []
          | DbAdd a -> a.scope, a.program, a.vars
        in
        if scope = Rocq_elpi_utils.Local || (List.exists (fun x -> is_in_section (Names.GlobRef.VarRef x)) vars) then None
        else Some o);
    }
  
    let in_file : Names.Id.t -> (program_name * (Digest.t * API.Compile.scoped_program)) -> Libobject.obj =
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
      
  let header_of_db qulid =
    Code.base @@ (SLMap.find qulid !db_name_src).sources_rev

  let ast_of_file qulid = SLMap.find qulid !file_name_src


  (* templates *)
  let lp_command_ast = Summary.ref ~name:("elpi-lp-command") None
  let in_lp_command_src : src -> Libobject.obj =
    let open Libobject in
    declare_object { (default_object "ELPI-LP-COMMAND") with
      load_function = (fun _ x -> lp_command_ast := Some x);
      classify_function = (fun _ -> Keep);
    }
  let load_command ~loc s =
    let elpi = ensure_initialized () in
    let ast = File {
      fname = s;
      fast = unit_from_file ~elpi ~loc ~base:EC.(empty_base ~elpi) s
    } in
    lp_command_ast := Some ast;
    Lib.add_leaf (in_lp_command_src ast)
  let command_init () =
    match !lp_command_ast with
    | None -> CErrors.user_err Pp.(str "Elpi CommandTemplate was not called")
    | Some ast -> ast

  let db_init_base ~loc =
    let elpi = ensure_initialized () in
    match command_init () with
    (* | File { fast = Full(_,base) } -> *)
    (*     let base = Signature (EC.signature base) in *)
    (*     base, extend_w_units ~loc ~base:EC.(empty_base ~elpi) [base] *)
    | File {fast=f}  ->
        let base = f in
        base, extend_w_units ~loc ~base:EC.(empty_base ~elpi) [base]
    | _ -> assert false

  let init_db qualid ~loc (sloc,s) =
    let base_sig, base = db_init_base ~loc in
    let elpi = ensure_initialized () in
    let unit = unit_from_string ~elpi ~base ~loc sloc s in
    add_to_db (DbInit {program=qualid; base=unit; base_sig})
    (* add_to_db qualid [base_sig] [] Rocq_elpi_utils.SuperGlobal *)
  
  let lp_tactic_ast = Summary.ref ~name:("elpi-lp-tactic") None
  let in_lp_tactic_ast : src -> Libobject.obj =
    let open Libobject in
    declare_object { (default_object "ELPI-LP-TACTIC") with
      load_function = (fun _ x -> lp_tactic_ast := Some x);
      classify_function = (fun _ -> Keep);
    }
  let load_tactic ~loc s =
    let elpi = ensure_initialized () in
    let ast = File {
      fname = s;
      fast = unit_from_file ~elpi ~loc ~base:(EC.empty_base ~elpi) s
    } in
    lp_tactic_ast := Some ast;
    Lib.add_leaf (in_lp_tactic_ast ast)
  let tactic_init () =
    match !lp_tactic_ast with
    | None -> CErrors.user_err Pp.(str "Elpi TacticTemplate was not called")
    | Some ast -> ast
  
  let init_program (loc,qualid) ~loc (init : src list) =
    if stage = Summary.Stage.Interp && Global.sections_are_opened () then
      CErrors.user_err Pp.(str "Program/Tactic/Db cannot be declared inside sections")
    else
      init_program qualid ~loc init
  
  let init_db (_,qualid) ~loc header =
    if stage = Summary.Stage.Interp && Global.sections_are_opened () then
      CErrors.user_err Pp.(str "Program/Tactic/Db cannot be declared inside sections")
    else if stage = Summary.Stage.Interp && match Global.current_modpath () with Names.ModPath.MPdot (Names.ModPath.MPfile _,_) -> true | _ -> false then
      CErrors.user_err Pp.(str "Program/Tactic/Db cannot be declared inside modules")
    else
    init_db qualid ~loc header
  ;;
    
  let accumulate p (v : src list) =
    if not (program_exists p) then begin
      CErrors.user_err Pp.(str "No Elpi Program named " ++ pr_qualified_name p);
    end;
    v |> List.iter (add_to_program p)
  
  let accumulate_to_db' (a : src list db_addition) =
    if not (db_exists a.program) then
      CErrors.user_err Pp.(str "No Elpi Db " ++ pr_qualified_name a.program);
    let {program; vars; scope} = a in
    List.iter (fun code ->
        add_to_db (DbAdd {program; vars; scope; code})
      ) a.code

  let accumulate_to_db program units vars ~scope =
    accumulate_to_db' {program; vars; scope; code = List.map (fun sast -> EmbeddedString {sast}) units}
  
  let in_stage = in_stage
  let stage = stage

  let db_inspect name =
    try Names.KNset.cardinal (SLMap.find name !db_name_src).units
  with Not_found -> -1
    
  let unit_from_ast ?error_header ~elpi ~base ~loc h ast =
    unit_from_ast ?error_header ~elpi ~base h ~loc ast ~flags:(cc_flags ())

let unit_signature_from_ast ~elpi ~base ~loc h ast =
  unit_signature_from_ast ~elpi ~base h ~loc ast ~flags:(cc_flags ())
  


module Visited = struct
  module Set = Names.KNset
  type t = {
    (* sigs : Set.t; *)
    full : Set.t;
    dbs : SLSet.t;
  }
  let empty = {
    (* sigs = Set.empty; *)
    full = Set.empty;
    dbs = SLSet.empty;
  }
  (* let add_sig n visited = { visited with sigs = Set.add n visited.sigs } *)
  let add_full n visited = { visited with (* sigs = Set.add n visited.sigs; *) full = Set.add n visited.full; }
  let add_db n visited = { visited with dbs = SLSet.add n visited.dbs }
  let add_unit u visited =
    match u with
    | Full (n, _) -> add_full n visited
    | Signature n -> visited

  let mem_unit u visited =
    match u with
    | Full (n, _) -> Set.mem n visited.full
    | Signature n -> false

  let mem_dbs n visited = SLSet.mem n visited.dbs
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
  r := Int.Map.add h (visited, prog,src) !r;
  visited, prog

let uncache b h r =
  let h = combine_hash b h in
  r := Int.Map.remove h !r


let eq_cunits = List.equal eq_cunit

let lookup_code b h src = lookup b h src compiler_cache_code (Code.eq eq_cunit eq_cunit eq_qualified_name) (Code.pp (fun _ _ -> ()) pp_qualified_name)
let lookup_chunk b h src = lookup b h src compiler_cache_chunk (Code.eq eq_cunit eq_cunits eq_qualified_name) (Code.pp (fun _ _ -> ()) pp_qualified_name)

let cache_code b h visited prog src = cache b h visited prog src compiler_cache_code
let cache_chunk b h visited prog src = cache b h visited prog src compiler_cache_chunk
  
let recache_code b h1 h2 visited p src =
  uncache b h1 compiler_cache_code;
  cache_code b h2 visited p src

let recache_chunk b h1 h2 visited p src =
  uncache b h1 compiler_cache_chunk;
  cache_chunk b h2 visited p src


let rec compile_code ~loc (src : (cunit, qualified_name) Code.t) : int * Visited.t * API.Compile.program =
  let h = Code.hash src in
  try
    if not @@ Code.cache src then raise Not_found;
    let visited, res = lookup_code 0 h src in
    (* let hsh = h in *)
    (* let () = Feedback.msg_debug Pp.(str "Cache lookup successful: " ++ int hsh) in *)
    h, visited, res
    (* raise Not_found *)
  with Not_found ->
  (* let hsh = h in *)
  (* let () = Feedback.msg_debug Pp.(str "Cache lookup failed: " ++ int hsh) in *)
  match src with
  | Code.Base { base = u } ->
    let visited = Visited.add_unit u Visited.empty in
    let elpi = ensure_initialized () in
    (* Feedback.msg_debug Pp.(str "Compiling base " ++ str (Format.asprintf "%a" pp_cunit u)); *)
    let prog = extend_w_units ~base:(EC.empty_base ~elpi) ~loc [u] in
    let visited, prog = cache_code 0 h visited prog src in
    hash_cunit u, visited, prog
  | Code.Snoc { prev; source } ->
    let (h, visited, base) as skip = compile_code ~loc prev in
    if not @@ Visited.mem_unit source visited then begin
      let visited = Visited.add_unit source visited in
      (* Feedback.msg_debug Pp.(str "Compiling " ++ str (Format.asprintf "%a" pp_cunit source)); *)
      let prog = extend_w_units ~base ~loc [source] in
      let h = combine_hash h (hash_cunit source) in
      if Code.cache src then
        let visited, prog = cache_code 0 h visited prog src in
        h, visited, prog
      else
        h, visited, prog
    end else
      skip
  | Code.Snoc_db {chunks=db_name; prev} ->
    let h, visited, base = compile_code ~loc prev in
    compile_db_name ~loc ~bvisited:visited ~base ~bhash:h db_name
and compile_db_name ~loc ~bvisited ~base ~bhash db_name =
  if not @@ SLSet.mem db_name bvisited.dbs then
    (* let () = Feedback.msg_debug Pp.(str "Compiling db code: " ++ pr_qualified_name db_name) in *)
    let src = Option.get @@ db_code_raw db_name in
    let h, visited, prog = compile_db ~loc ~bvisited ~base ~bhash src in
    let visited = Visited.add_db db_name visited in
    h, visited, prog
  else
    (* let () = Feedback.msg_debug Pp.(str "Skipping db code: " ++ pr_qualified_name db_name) in *)
    bhash, bvisited, base
and compile_db ~loc ~bvisited ~base ~bhash src =
  let h = Code.hash src in
  try
    if not @@ Code.cache src then raise Not_found;
    let visited, res = lookup_chunk bhash h src in
    (* let hsh = h in *)
    (* let () = Feedback.msg_debug Pp.(str "Cache lookup successful: " ++ int hsh) in *)
    h, visited, res
    (* raise Not_found *)
  with Not_found ->
  (* let hsh = h in *)
  (* let () = Feedback.msg_debug Pp.(str "Cache lookup failed: " ++ int hsh) in *)
  match src with
  | Code.Base { base = us } ->
    let visited = bvisited in
    let us = List.filter (fun u -> not @@ Visited.mem_unit u visited) us in
    let visited = List.fold_left (fun vis u -> Visited.add_unit u vis) visited us in (* TODO: [List.rev us]? *)
    let prog = extend_w_units ~base ~loc us in
    let bhash = List.fold_left (fun b u -> combine_hash b (hash_cunit u)) bhash us in
    let visited, prog = cache_chunk bhash h visited prog src in
    bhash, visited, prog
  | Code.Snoc { source; prev } ->
    let (bhash_new, visited, base) as skip = compile_db ~loc ~bvisited ~base ~bhash prev in
    if not @@ Visited.mem_unit source visited then begin
      let visited = Visited.add_unit source visited in
      (* Feedback.msg_debug Pp.(str "Compiling " ++ str (Format.asprintf "%a" pp_cunit source)); *)
      let prog = extend_w_units ~base ~loc [source] in
      let bhash_new = combine_hash (hash_cunit source) bhash_new in
      if Code.cache src then
        let visited, prog = cache_chunk bhash h visited prog src in
        bhash_new, visited, prog
      else
        bhash_new, visited, prog
    end else
      skip
  | Code.Snoc_db { chunks=db_name; prev } ->
    let bhash, bvisited, base = compile_db ~loc ~bvisited ~base ~bhash prev in
    compile_db_name ~loc ~bvisited ~base ~bhash db_name
let compile_prog ~loc prog =
  compile_code ~loc prog

let compile_db ~loc db_prog =
  let elpi = ensure_initialized () in
  let base = EC.empty_base ~elpi in
  let bvisited = Visited.empty in
  let bhash = 0 in
  let (_, _, code) = compile_db ~loc ~bvisited ~base ~bhash db_prog in
  code

let get_and_compile ~loc ?even_if_empty name : (EC.program * bool) option =
  let t = Unix.gettimeofday () in
  let res = code ?even_if_empty name |> Option.map (fun src ->
    (* Format.eprintf "compile %a = %a" pp_qualified_name name (Code.pp Chunk.pp) src; *)
    let bhash, visited, prog = compile_prog ~loc src in
    let new_hash = Code.hash src in
    let old_hash = try SLMap.find name !programs_tip with Not_found -> 0 in
    programs_tip := SLMap.add name new_hash !programs_tip;
    let _, prog = recache_code 0 old_hash new_hash visited prog src in
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
    | Some db ->
      compile_db ~loc db

  let get_and_compile_any ~loc name : EC.program =
    if db_exists name then
      get_and_compile_existing_db ~loc name
    else
      get_and_compile ~loc ~even_if_empty:true name |> Option.get |> fst
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
        let units = List.map (fun x -> unit_from_ast ~error_header:(Format.asprintf "accumulating clause to %s" (String.concat "." dbname)) ~elpi ~base None ~loc (EC.scope ~elpi x)) asts in
        dbname,units,vs,scope) in
    clauses_to_add |> List.iter (fun (dbname,units,vs,scope) ->
        accumulate_to_db dbname units vs ~scope
      ))

  let accumulate_to_db' ~loc data =
  accumulate_to_db' data;
  handle_elpi_compiler_errors ~loc (fun () -> 
    get_and_compile_any ~loc data.program |> ignore)

let accumulate_to_db ~loc name sources vars ~scope =
  accumulate_to_db name sources vars ~scope;
  handle_elpi_compiler_errors ~loc (fun () -> 
    get_and_compile_any ~loc name |> ignore)
  
  let accumulate ~loc name sources =
    accumulate name (sources:src list);
    handle_elpi_compiler_errors ~loc (fun () -> 
      get_and_compile ~even_if_empty:false ~loc:(Loc.make_loc (0,0)) name |> ignore)

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
      let units = List.map (fun x -> unit_from_ast ~error_header:(Format.asprintf "accumulating clause to %s" (String.concat "." dbname)) ~elpi ~base None ~loc (EC.scope ~elpi x)) asts in
      dbname,units,vs,scope) in
  clauses_to_add |> List.iter (fun (dbname,units,vs,scope) ->
    accumulate_to_db dbname units vs ~scope))
  
let () = Rocq_elpi_builtins.set_accumulate_text_to_db_interp (fun ~loc n txt scope ->
      let elpi = ensure_initialized () in
      let base = get_and_compile_existing_db ~loc n in
      let u = unit_from_string ~elpi ~base ~loc (of_coq_loc loc) txt in
  accumulate_to_db n [u] [] ~scope)

let accumulate_to_db' ~loc data =
  accumulate_to_db' data;
  handle_elpi_compiler_errors ~loc (fun () -> 
    get_and_compile_any ~loc data.program |> ignore)

let accumulate_to_db ~loc name sources vars ~scope =
  accumulate_to_db name sources vars ~scope;
  handle_elpi_compiler_errors ~loc (fun () -> 
    get_and_compile_any ~loc name |> ignore)

let accumulate ~loc name sources =
  accumulate name (sources:src list);
  handle_elpi_compiler_errors ~loc (fun () -> 
    get_and_compile_any ~loc name |> ignore)

let init_program name ~loc sources =
  init_program name ~loc (sources:src list);
  handle_elpi_compiler_errors ~loc (fun () -> 
    get_and_compile ~even_if_empty:true ~loc (snd name) |> ignore)

end

let document_builtins () =
  API.BuiltIn.document_file coq_interp_builtins;
  API.BuiltIn.document_file coq_synterp_builtins;
  API.BuiltIn.document_file ~header:"% Generated file, do not edit" elpi_builtins

