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
  try EC.unit ~elpi ~flags:(cc_flags ()) (EP.program ~elpi ~print_accumulated_files:false [x])
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

let assemble_units ~elpi units =
  try EC.assemble ~elpi units
  with EC.CompileError(oloc, msg) ->
    let loc = Option.map Coq_elpi_utils.to_coq_loc oloc in
    CErrors.user_err ?loc ~hdr:"elpi" (Pp.str msg)

let extend_w_units ~base units =
  try EC.extend ~base units
  with EC.CompileError(oloc, msg) ->
    let loc = Option.map Coq_elpi_utils.to_coq_loc oloc in
    CErrors.user_err ?loc ~hdr:"elpi" (Pp.str msg)

type qualified_name = string list
let compare_qualified_name = Pervasives.compare
let pr_qualified_name = Pp.prlist_with_sep (fun () -> Pp.str".") Pp.str
let show_qualified_name = String.concat "."
let _pp_qualified_name fmt l = Format.fprintf fmt "%s" (String.concat "." l)

type expr_record_decl = {
  name : qualified_name;
  parameters : Constrexpr.local_binder_expr list;
  sort : Constrexpr.sort_expr option;
  constructor : Names.Id.t option;
  fields : (Vernacexpr.local_decl_expr * Vernacexpr.record_field_attr) list
}
let pr_expr_record_decl _ _ { name; sort; constructor; fields } = Pp.str "TODO: pr_expr_record_decl"

type expr_indt_decl = {
  finiteness : Vernacexpr.inductive_kind;
  name : qualified_name;
  parameters : Constrexpr.local_binder_expr list;
  non_uniform_parameters : Constrexpr.local_binder_expr list;
  arity : Constrexpr.constr_expr option;
  constructors : (Names.lident * Constrexpr.constr_expr) list;
}
let pr_expr_indt_decl _ _ _ = Pp.str "TODO: pr_expr_indt_decl"

type expr_constant_decl = {
  name : qualified_name;
  typ : Constrexpr.local_binder_expr list * Constrexpr.constr_expr option;
  body : Constrexpr.constr_expr option;
}
let pr_expr_constant_decl _ _ { name; typ; body } = Pp.str "TODO: pr_expr_constant_decl"
let pr_expr_context _ _ _ = Pp.str "TODO: pr_expr_context"

type ('a,'b,'c,'d,'e) arg =
  | Int of int
  | String of string
  | Qualid of qualified_name
  | DashQualid of qualified_name
  | Term of 'a
  | RecordDecl of 'b
  | IndtDecl of 'c
  | ConstantDecl of 'd
  | Context of 'e

type raw_arg = (Constrexpr.constr_expr,  expr_record_decl, expr_indt_decl, expr_constant_decl,Constrexpr.local_binder_expr list) arg
type glob_arg = (Genintern.glob_constr_and_expr, Coq_elpi_goal_HOAS.glob_record_decl, Coq_elpi_goal_HOAS.glob_indt_decl, Coq_elpi_goal_HOAS.glob_constant_decl,Coq_elpi_goal_HOAS.glob_context_decl) arg
type parsed_arg = (Coq_elpi_goal_HOAS.parsed_term, Coq_elpi_goal_HOAS.parsed_record_decl, Coq_elpi_goal_HOAS.parsed_indt_decl, Coq_elpi_goal_HOAS.parsed_constant_decl, Coq_elpi_goal_HOAS.parsed_context_decl) arg


let pr_arg f g h i j = function
  | Int n -> Pp.int n
  | String s -> Pp.qstring s
  | Qualid s -> pr_qualified_name s
  | DashQualid s -> Pp.(str"- " ++ pr_qualified_name s)
  | Term s -> f s
  | RecordDecl s -> g s
  | IndtDecl s -> h s
  | ConstantDecl s -> i s
  | Context c -> j c

let push_name x = function
  | Names.Name.Name id ->
      let decl = Context.Named.Declaration.LocalAssum (Context.make_annot id Sorts.Relevant, Constr.mkProp) in
      { x with Genintern.genv = Environ.push_named decl x.Genintern.genv }
  | _ -> x

let push_gdecl (name,_,_,_) x = push_name x name

let push_glob_ctx glob_ctx x =
  List.fold_right push_gdecl glob_ctx x


let push_inductive_in_intern_env intern_env name params arity user_impls =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, ty = Pretyping.understand_tcc env sigma ~expected_type:Pretyping.IsType (Coq_elpi_utils.mk_gforall arity params) in
  Constrintern.compute_internalization_env env sigma ~impls:intern_env
    Constrintern.Inductive [name] [ty] [user_impls]

let intern_tactic_constr = Ltac_plugin.Tacintern.intern_constr

let intern_global_constr { Ltac_plugin.Tacintern.genv = env } ?(intern_env=Constrintern.empty_internalization_env) t =
  let sigma = Evd.from_env env in
  Constrintern.intern_gen Pretyping.WithoutTypeConstraint env sigma ~impls:intern_env ~pattern_mode:false ~ltacvars:Constrintern.empty_ltac_sign t

let intern_global_constr_ty { Ltac_plugin.Tacintern.genv = env } ?(intern_env=Constrintern.empty_internalization_env) t =
  let sigma = Evd.from_env env in
  Constrintern.intern_gen Pretyping.IsType env sigma ~impls:intern_env ~pattern_mode:false ~ltacvars:Constrintern.empty_ltac_sign t

let intern_global_context { Ltac_plugin.Tacintern.genv = env } ?(intern_env=Constrintern.empty_internalization_env) ctx =
  Constrintern.intern_context env ~bound_univs:UnivNames.empty_binders intern_env ctx

let subst_global_constr s t = Detyping.subst_glob_constr (Global.env()) s t
let subst_global_decl s (n,bk,ot,t) =
  (n,bk,Option.map (subst_global_constr s) ot,subst_global_constr s t)

let sep_last_qualid = function
  | [] -> "_", []
  | l -> CList.sep_last l

let intern_record_decl glob_sign { name; sort; parameters; constructor; fields } =
  let name, space = sep_last_qualid name in
  let sort = match sort with
    | Some x -> Constrexpr.CSort x
    | None -> Constrexpr.(CSort (Glob_term.UAnonymous {rigid=true})) in
  let intern_env, params = intern_global_context glob_sign parameters in
  let glob_sign_params = push_glob_ctx params glob_sign in
  let params = List.rev params in
  let arity = intern_global_constr_ty glob_sign_params @@ CAst.make sort in
  let _, fields =
    List.fold_left (fun (gs,acc) -> function
    | Vernacexpr.AssumExpr ({ CAst.v = name } as fn,bl,x), { Vernacexpr.rf_subclass = inst; rf_priority = pr; rf_notation = nots; rf_canonical = canon } ->
        if nots <> [] then Coq_elpi_utils.nYI "notation in record fields";
        if pr <> None then Coq_elpi_utils.nYI "priority in record fields";
        let atts = { Coq_elpi_HOAS.is_canonical = canon; is_coercion = inst <> Vernacexpr.NoInstance; name } in
        let x = if bl = [] then x else Constrexpr_ops.mkCProdN bl x in
        push_name gs fn.CAst.v, (intern_global_constr_ty gs x, atts) :: acc
    | Vernacexpr.DefExpr _, _ -> Coq_elpi_utils.nYI "DefExpr")
        (glob_sign_params,[]) fields in
  { Coq_elpi_goal_HOAS.name = (space, Names.Id.of_string name); arity; params; constructorname = constructor; fields = List.rev fields }

let subst_record_decl s { Coq_elpi_goal_HOAS.name; arity; params; constructorname; fields } =
  let arity = subst_global_constr s arity in
  let fields = List.map (fun (t,att) -> subst_global_constr s t,att) fields in
  { Coq_elpi_goal_HOAS.name; arity; params; constructorname; fields }

let intern_indt_decl glob_sign { finiteness; name; parameters; non_uniform_parameters; arity; constructors } =
  let name, space = sep_last_qualid name in
  let name = Names.Id.of_string name in
  let indexes = match arity with
    | Some x -> x
    | None -> CAst.make Constrexpr.(CSort (Glob_term.UAnonymous {rigid=true})) in
  let intern_env, params = intern_global_context glob_sign parameters in
  let intern_env, nuparams = intern_global_context glob_sign ~intern_env non_uniform_parameters in
  let params = List.rev params in
  let nuparams = List.rev nuparams in
  let allparams = params @ nuparams in
  let user_impls : Impargs.manual_implicits = List.map Coq_elpi_utils.manual_implicit_of_gdecl allparams in
  let glob_sign_params = push_glob_ctx allparams glob_sign in
  let arity = intern_global_constr_ty glob_sign_params indexes in
  let glob_sign_params_self = push_name glob_sign_params (Names.Name name) in
  let intern_env = push_inductive_in_intern_env intern_env name allparams arity user_impls in
  let constructors =
    List.map (fun (id,ty) -> id.CAst.v,
      intern_global_constr_ty glob_sign_params_self ~intern_env ty) constructors in
  { Coq_elpi_goal_HOAS.finiteness; name = (space, name); arity; params; nuparams; constructors }

let subst_indt_decl s { Coq_elpi_goal_HOAS.finiteness; name; arity; params; nuparams; constructors } =
  let arity = subst_global_constr s arity in
  let params = List.map (subst_global_decl s) params in
  let nuparams = List.map (subst_global_decl s) nuparams in
  let constructors = List.map (fun (id,t) -> id, subst_global_constr s t) constructors in
  { Coq_elpi_goal_HOAS.finiteness; name; arity; params; nuparams; constructors }

let expr_hole = CAst.make @@ Constrexpr.CHole(None,Namegen.IntroAnonymous,None)

let bk_of_bk = function
  | Constrexpr.Default x -> x
  | Constrexpr.Generalized _ -> Coq_elpi_utils.nYI "Constrexpr.Generalized"

let intern_context_decl glob_sign fields =
  let _, fields =
    List.fold_left (fun (gs,acc) -> function
      | Constrexpr.CLocalAssum (l,bk,ty) ->
          let ty = intern_global_constr_ty gs ty in
          List.fold_left push_name gs (List.map (fun x -> x.CAst.v) l),
            (List.rev l |> List.map (fun { CAst.v = name } -> name, bk_of_bk bk, None, ty)) @ acc
      | Constrexpr.CLocalDef ({ CAst.v = name } as fn,bo,ty) ->
          let intern = intern_global_constr_ty gs in
          let ty = Option.default expr_hole ty in
          push_name gs fn.CAst.v, (name, Glob_term.Explicit, Some (intern bo), intern ty) :: acc
      | Constrexpr.CLocalPattern _ -> Coq_elpi_utils.nYI "CLocalPattern")
     (glob_sign,[]) fields in
  List.rev fields

let subst_context_decl s l =
  let subst = subst_global_constr s in
  l |> List.map (fun (name,bk,bo,ty) -> name, bk, Option.map subst bo, subst ty)

let intern_constant_decl glob_sign { name; typ = (params,typ); body } =
  let name, space = sep_last_qualid name in
  let _intern_env, params = intern_global_context glob_sign params in
  let glob_sign_params = push_glob_ctx params glob_sign in
  let params = List.rev params in
  let typ = Option.default expr_hole typ in
  let typ = intern_global_constr_ty glob_sign_params typ in
  let body = Option.map (intern_global_constr glob_sign_params) body in
  { Coq_elpi_goal_HOAS.name = (space, Names.Id.of_string name); params; typ; body }

let subst_constant_decl s { Coq_elpi_goal_HOAS.name; params; typ; body } =
  let typ = subst_global_constr s typ in
  let params = List.map (subst_global_decl s) params in
  let body = Option.map (subst_global_constr s) body in
  { Coq_elpi_goal_HOAS.name; params; typ; body }

let glob_arg glob_sign = function
  | Qualid _ as x -> x
  | DashQualid _ as x -> x
  | Int _ as x -> x
  | String _ as x -> x
  | Term t -> Term (intern_tactic_constr glob_sign t)
  | RecordDecl t -> RecordDecl (intern_record_decl glob_sign t)
  | IndtDecl t -> IndtDecl (intern_indt_decl glob_sign t)
  | ConstantDecl t -> ConstantDecl (intern_constant_decl glob_sign t)
  | Context c -> Context (intern_context_decl glob_sign c)

let interp_arg ist evd = function
  | Qualid _ as x -> evd.Evd.sigma, x
  | DashQualid _ as x -> evd.Evd.sigma, x
  | Int _ as x -> evd.Evd.sigma, x
  | String _ as x -> evd.Evd.sigma, x
  | Term t -> evd.Evd.sigma, (Term(ist,t))
  | RecordDecl t -> evd.Evd.sigma, (RecordDecl(ist,t))
  | IndtDecl t -> evd.Evd.sigma, (IndtDecl(ist,t))
  | ConstantDecl t -> evd.Evd.sigma, (ConstantDecl(ist,t))
  | Context c -> evd.Evd.sigma, (Context(ist,c))

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

  val get : qualified_name -> Compile.compilation_unit list * Compile.compilation_unit list (* code , db *)

  val create_program : program_name -> src -> unit
  val create_db : program_name -> src -> unit

  val set_current_program : qualified_name -> unit
  val current_program : unit -> qualified_name
  val accumulate : qualified_name -> src list -> unit
  val accumulate_to_db : qualified_name -> Compile.compilation_unit list -> local:bool -> unit

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
let compare_src = Pervasives.compare

module SrcSet = Set.Make(struct type t = src let compare = compare_src end)

let current_program = Summary.ref ~name:"elpi-cur-program-name" None

let program_src : (SrcSet.t * src list) SLMap.t ref =
  Summary.ref ~name:"elpi-programs" SLMap.empty
let program_exists name = SLMap.mem name !program_src

module KSet = Set.Make(Names.KerName)
let db_name_src : (KSet.t * (Names.KerName.t * EC.compilation_unit list) list) SLMap.t ref =
  Summary.ref ~name:"elpi-db" SLMap.empty
let db_exists name = SLMap.mem name !db_name_src

let ast_of_src = function
  | File { fast = a } -> [`Static,a]
  | EmbeddedString { sast = a } -> [`Static,a]
  | Database name ->
     try
       match List.(flatten (map snd (snd (SLMap.find name !db_name_src)))) with
       | header :: clauses ->
           (`Static,header) :: List.map (fun x -> `Dynamic,x) clauses
       | [] -> assert false
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
      SrcSet.empty, []

let append_to_prog name l =
  let seen, prog = get name in
  let rec aux seen acc = function
    | [] -> seen, List.rev acc
    | x :: xs when SrcSet.mem x seen -> aux seen acc xs
    | x :: xs -> aux (SrcSet.add x seen) (x :: acc) xs in
  let seen, l = aux seen [] l in
  let prog = prog @ l in
  seen, prog

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

let append_to_db name (kname,data as l) =
  let seen, db = try SLMap.find name !db_name_src with Not_found -> KSet.empty, [] in
  if KSet.mem kname seen then seen, db
  else
    let seen = KSet.add kname seen in
    seen, db @ [l]

type snippet = {
  program : qualified_name;
  code : EC.compilation_unit list;
  local : bool;
}

let in_db : snippet -> Libobject.obj =
  let cache ((_,kname), { program = name; code = p; _ }) =
    db_name_src := SLMap.add name (append_to_db name (kname,p)) !db_name_src in
  let import i o = if Int.equal i 1 then cache o in
  Libobject.declare_object @@ { (Libobject.default_object "ELPI-DB") with
    Libobject.classify_function = (fun ({ local; _ } as o) ->
       if local then Libobject.Dispose else Libobject.Keep o);
    Libobject.cache_function  = cache;
    Libobject.subst_function = (fun _ -> CErrors.user_err Pp.(str"elpi: No functors yet"));
    Libobject.open_function = Libobject.simple_open import;
}

let add_to_db program code local =
  Lib.add_anonymous_leaf (in_db { program; code; local })

let lp_command_ast = Summary.ref ~name:"elpi-lp-command" None
let in_lp_command_src : src -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI-LP-COMMAND") with
    Libobject.load_function = (fun _ (_,x) -> lp_command_ast := Some x);
}
let load_command s =
  let elpi = ensure_initialized () in
  let ast = File {
    fname = s;
    fast = unit_from_file ~elpi s
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
    fast = unit_from_file ~elpi s
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
    add_to_db qualid (List.map snd @@ ast_of_src init) false
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

let get x =
  let chunks = List.(flatten @@ map ast_of_src (snd (get ~fail_if_not_exists:true x))) in
  static_prefix [] chunks

let lp_checker_ast = Summary.ref ~name:"elpi-lp-checker" None
let in_lp_checker_ast : EC.compilation_unit list -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI-LP-CHECKER") with
    Libobject.load_function = (fun _ (_,x) -> lp_checker_ast := Some x);
}
let load_checker s =
  let elpi = ensure_initialized () in
  let basic_checker = unit_from_string ~elpi (Elpi.API.Ast.Loc.initial "(elpi-checker)") Elpi.Builtin_checker.code in
  let coq_checker = unit_from_file ~elpi s in
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
  let ast = unit_from_file ~elpi s in
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

let accumulate_to_db p v ~local =
  if not (db_exists p) then
    CErrors.user_err Pp.(str "No Elpi Db " ++ pr_qualified_name p);
  add_to_db p v local

end

let current_program_begin_run = ref None

let () = Coq_elpi_builtins.set_accumulate_to_db (Programs.ensure_initialized, (fun n x ~local -> Programs.accumulate_to_db n [x] ~local), (fun () -> Option.get !current_program_begin_run))
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

let get_and_compile name =
  let core_units, extra_units = get name in
  let prog = compile name core_units extra_units in
  prog

let run_static_check query =
  let checker = compile ["Elpi";"Typecheck"] (checker()) [] in
  (* We turn a failure into a proper error in etc/coq-elpi_typechecker.elpi *)
  ignore (EC.static_check ~checker query)

let run ~tactic_mode ~static_check program query =
  current_program_begin_run := Some program;
  let t1 = Unix.gettimeofday () in
  let query =
    match query with
    | `Ast query_ast -> EC.query program query_ast
    | `Fun query_builder -> API.RawQuery.compile program query_builder in
  let t2 = Unix.gettimeofday () in
  API.Setup.trace [];
  if static_check then run_static_check query;
  let t3 = Unix.gettimeofday () in
  API.Setup.trace !trace_options;
  Coq_elpi_builtins.tactic_mode := tactic_mode;
  let exe = EC.optimize query in
  let t4 = Unix.gettimeofday () in
  let rc = API.Execute.once ~max_steps:!max_steps exe in
  let t5 = Unix.gettimeofday () in
  if !Flags.debug then
    Feedback.msg_notice (Pp.str @@ Printf.sprintf "Elpi: query-compilation:%1.4f static-check:%1.4f optimization:%1.4f runtime:%1.4f\n"
      (t2 -. t1) (t3 -. t2) (t4 -. t3) (t5 -. t4));
  rc
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
    List.iter (fun (dbname,ast,local) ->
      let unit = EC.unit ~elpi ~flags:(cc_flags()) ast in
      accumulate_to_db dbname [unit] ~local) clauses_to_add
;;

let run_in_program ?(program = current_program ()) (loc, query) =
  let _ = ensure_initialized () in
  let program = get_and_compile program in
  let query_ast = `Ast (parse_goal loc query) in
  run_and_print ~tactic_mode:false ~print:true ~static_check:true program query_ast
;;

let typecheck_program ?(program = current_program ()) () =
  let program = get_and_compile program in
  let query_ast = parse_goal (API.Ast.Loc.initial "(typecheck)") "true." in
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
  | IndtDecl t -> Coq_elpi_goal_HOAS.IndtDecl t
  | ConstantDecl t -> Coq_elpi_goal_HOAS.ConstantDecl t
  | Context c -> Coq_elpi_goal_HOAS.Context c

let mainc = ET.Constants.declare_global_symbol "main"
let attributesc = ET.Constants.declare_global_symbol "attributes"

let run_program loc name ~atts args =
  let args = args
    |> List.map (glob_arg (Genintern.empty_glob_sign (Global.env())))
    |> List.map (interp_arg (Ltac_plugin.Tacinterp.default_ist ()) Evd.({ sigma = from_env (Global.env()); it = 0 }))
    |> List.map snd in
  let args = args |> List.map to_arg in
  let query ~depth state =
    let state, atts, _ = EU.map_acc (Coq_elpi_builtins.attribute.API.Conversion.embed ~depth) state atts in
    let state, args = CList.fold_left_map
      (Coq_elpi_goal_HOAS.in_elpi_global_arg ~depth Coq_elpi_HOAS.(mk_coq_context ~options:default_options state))
      state args in
    let atts = ET.mkApp attributesc (EU.list_to_lp_list atts) [] in
    state, (Coq_elpi_utils.of_coq_loc loc, ET.mkApp ET.Constants.implc atts [ET.mkApp mainc (EU.list_to_lp_list args) []]) in
  let program = get_and_compile name in
  run_and_print ~tactic_mode:false ~print:false ~static_check:false program (`Fun query)
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
  let program = get_and_compile name in
  let query_ast = parse_goal (API.Ast.Loc.initial "(print)") "true." in
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
  run_and_print ~tactic_mode:false ~print:false ~static_check:false (compile ["Elpi";"Print"] [printer ()] []) (`Fun q)
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
  let program = get_and_compile program in
  match run ~tactic_mode:true ~static_check:false program query with
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
  let program = get_and_compile program in
  match run ~tactic_mode:true ~static_check:true program query with
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
        fast = unit_from_file ~elpi fname;
      }) s in
    accumulate program new_src_ast
  with Failure s ->  CErrors.user_err Pp.(str s)
 ;;

let accumulate_string ?(program=current_program()) (loc,s) =
  let elpi = ensure_initialized () in
  let new_ast = unit_from_string ~elpi loc s in
  if db_exists program then
    accumulate_to_db program [new_ast] ~local:false
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


let in_exported_program : (qualified_name * string * (Loc.t,Loc.t,Loc.t) Genarg.ArgT.tag * (raw_arg,glob_arg,parsed_arg) Genarg.ArgT.tag) -> Libobject.obj =
  Libobject.declare_object @@ Libobject.global_object_nodischarge "ELPI-EXPORTED"
    ~cache:(fun (_,(p,p_str,tag_loc,tag_arg)) ->
    Vernacextend.vernac_extend
      ~command:("Elpi "^p_str)
      ~classifier:(fun _ -> Vernacextend.classify_as_sideeff)
      ?entry:None
      [ Vernacextend.TyML (false,
          Vernacextend.TyTerminal (p_str,
            Vernacextend.TyNonTerminal (Extend.TUentry tag_loc,
            Vernacextend.TyNonTerminal (Extend.TUlist0 (Extend.TUentry tag_arg),
            Vernacextend.TyNil))),
          (fun loc args ~atts -> Vernacextend.VtDefault (fun () ->
              run_program loc p ~atts args)),
          None)])
    ~subst:(Some (fun _ -> CErrors.user_err Pp.(str"elpi: No functors yet")))

let export_command p tag_loc tag_arg =
  Lib.add_anonymous_leaf (in_exported_program (p,String.concat "." p,tag_loc,tag_arg))

