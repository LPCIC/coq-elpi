(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
module E = API.RawData
module CD = API.RawOpaqueData

open Coq_elpi_utils
open Coq_elpi_HOAS
open Names

type raw_term = Constrexpr.constr_expr
type glob_term = Genintern.glob_constr_and_expr
type top_term =
  Ltac_plugin.Tacinterp.interp_sign * Genintern.glob_constr_and_expr


type raw_record_decl = {
  name : qualified_name;
  parameters : Constrexpr.local_binder_expr list;
  sort : Constrexpr.sort_expr option;
  constructor : Names.Id.t option;
  fields : (Vernacexpr.local_decl_expr * Vernacexpr.record_field_attr) list
}
type glob_record_decl = {
  name : string list * Names.Id.t;
  constructorname : Names.Id.t option;
  params : Glob_term.glob_decl list;
  arity : Glob_term.glob_constr;
  fields : (Glob_term.glob_constr * Coq_elpi_HOAS.record_field_spec) list
}
type top_record_decl = Geninterp.interp_sign * glob_record_decl
let pr_raw_record_decl _ _ _ = Pp.str "TODO: pr_raw_record_decl"
let pr_glob_record_decl _ _ _ = Pp.str "TODO: pr_glob_record_decl"
let pr_top_record_decl _ _ _ = Pp.str "TODO: pr_top_record_decl"

type raw_indt_decl = {
  finiteness : Vernacexpr.inductive_kind;
  name : qualified_name;
  parameters : Constrexpr.local_binder_expr list;
  non_uniform_parameters : Constrexpr.local_binder_expr list;
  arity : Constrexpr.constr_expr option;
  constructors : (Names.lident * Constrexpr.constr_expr) list;
}
type glob_indt_decl = {
  finiteness : Vernacexpr.inductive_kind;
  name : string list * Names.Id.t;
  arity : Glob_term.glob_constr;
  params : Glob_term.glob_decl list;
  nuparams : Glob_term.glob_decl list;
  constructors : (Names.Id.t * Glob_term.glob_constr) list;
}
type top_indt_decl = Geninterp.interp_sign * glob_indt_decl
let pr_raw_indt_decl _ _ _ = Pp.str "TODO: pr_raw_indt_decl"
let pr_glob_indt_decl _ _ _ = Pp.str "TODO: pr_glob_indt_decl"
let pr_top_indt_decl _ _ _ = Pp.str "TODO: pr_top_indt_decl"

type raw_constant_decl = {
  name : qualified_name;
  typ : Constrexpr.local_binder_expr list * Constrexpr.constr_expr option;
  body : Constrexpr.constr_expr option;
  red : Genredexpr.raw_red_expr option;
}
type _glob_constant_decl = {
  name : string list * Names.Id.t;
  params : Glob_term.glob_decl list;
  typ : Glob_term.glob_constr;
  body : Glob_term.glob_constr option;
}
type glob_constant_decl = Genintern.glob_sign * raw_constant_decl
type top_constant_decl = Geninterp.interp_sign * glob_constant_decl

let pr_raw_constant_decl _ _ _ = Pp.str "TODO: pr_raw_constant_decl"
let pr_glob_constant_decl _ _ _ = Pp.str "TODO: pr_glob_constant_decl"
let pr_top_constant_decl _ _ _ = Pp.str "TODO: pr_top_constant_decl"


type raw_context_decl = Constrexpr.local_binder_expr list
type glob_context_decl = Glob_term.glob_decl list
type top_context_decl = Geninterp.interp_sign * glob_context_decl

let pr_raw_context_decl _ _ _ = Pp.str "TODO: pr_raw_context_decl"
let pr_glob_context_decl _ _ _ = Pp.str "TODO: pr_glob_context_decl"
let pr_top_context_decl _ _ _ = Pp.str "TODO: pr_top_context_decl"

type raw_ltac_arg = raw_term
type glob_ltac_arg = Glob_term.glob_constr
type top_ltac_arg = Geninterp.interp_sign * Names.Id.t

let pr_raw_ltac_arg _ _ _ = Pp.str "TODO: pr_raw_ltac_arg"
let pr_glob_ltac_arg _ _ _ = Pp.str "TODO: pr_glob_ltac_arg"
let pr_top_ltac_arg _ _ _ = Pp.str "TODO: pr_top_ltac_arg"


type ltac_ty = Int | String | Term | List of ltac_ty

type tac
type cmd

type ('a,'b,'c,'d,'e,'f,_) arg =
  | Int : int            -> ('a,'b,'c,'d,'e,'f,_  ) arg
  | String : string      -> ('a,'b,'c,'d,'e,'f,_  ) arg
  | Term : 'a            -> ('a,'b,'c,'d,'e,'f,_  ) arg
  | LTac : ltac_ty * 'f  -> ('a,'b,'c,'d,'e,'f,tac) arg
  | RecordDecl : 'b      -> ('a,'b,'c,'d,'e,'f,cmd) arg
  | IndtDecl : 'c        -> ('a,'b,'c,'d,'e,'f,cmd) arg
  | ConstantDecl : 'd    -> ('a,'b,'c,'d,'e,'f,cmd) arg
  | Context : 'e         -> ('a,'b,'c,'d,'e,'f,cmd) arg

type 'a raw_arg = (raw_term,  raw_record_decl, raw_indt_decl, raw_constant_decl,raw_context_decl,raw_ltac_arg,'a) arg
type ('a,'b) glob_arg = ('b, glob_record_decl, glob_indt_decl, glob_constant_decl,glob_context_decl,Glob_term.glob_constr,'a) arg
type top_arg = (top_term, top_record_decl, top_indt_decl, top_constant_decl, top_context_decl, top_ltac_arg,cmd) arg
type top_tac_arg = (top_term, top_record_decl, top_indt_decl, top_constant_decl, top_context_decl, top_ltac_arg,tac) arg

 let pr_arg f g h i j x = match x with
  | Int n -> Pp.int n
  | String s -> Pp.qstring s
  | Term s -> f s
  | RecordDecl s -> g s
  | IndtDecl s -> h s
  | ConstantDecl s -> i s
  | Context c -> j c

let pr_tac_arg f k x = match x with
  | Int n -> Pp.int n
  | String s -> Pp.qstring s
  | Term s -> f s
  | LTac(_, s) -> k s

let pr_glob_constr_and_expr env sigma = function
  | (_, Some c) ->
    Ppconstr.pr_constr_expr env sigma c
  | (c, None) ->
    Printer.pr_glob_constr_env env sigma c

let pp_raw_arg env sigma =
  pr_arg
    (Ppconstr.pr_constr_expr env sigma)
    (pr_raw_record_decl env sigma)
    (pr_raw_indt_decl env sigma)
    (pr_raw_constant_decl env sigma)
    (pr_raw_context_decl env sigma)

let pp_raw_tac_arg env sigma =
  pr_tac_arg
    (Ppconstr.pr_constr_expr env sigma)
    (pr_raw_ltac_arg env sigma)
    
let pp_glob_arg env sigma =
  pr_arg
    (pr_glob_constr_and_expr env sigma)
    (pr_glob_record_decl env sigma)
    (pr_glob_indt_decl env sigma)
    (pr_glob_constant_decl env sigma)
    (pr_glob_context_decl env sigma)

let pp_glob_tac_arg env sigma =
  pr_tac_arg
    (pr_glob_constr_and_expr env sigma)
    (pr_glob_ltac_arg env sigma)
    
let pp_top_arg env sigma =
  pr_arg
    (fun (_,x) -> pr_glob_constr_and_expr env sigma x)
    (pr_top_record_decl env sigma)
    (pr_top_indt_decl env sigma)
    (pr_top_constant_decl env sigma)
    (pr_top_context_decl env sigma)

let pp_top_tac_arg env sigma =
  pr_tac_arg
    (fun (_,x) -> pr_glob_constr_and_expr env sigma x)
    (pr_top_ltac_arg env sigma)
      
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

let intern_global_constr { Ltac_plugin.Tacintern.genv = env } ~intern_env t =
  let sigma = Evd.from_env env in
  Constrintern.intern_gen Pretyping.WithoutTypeConstraint env sigma ~impls:intern_env ~pattern_mode:false ~ltacvars:Constrintern.empty_ltac_sign t

let intern_global_constr_ty { Ltac_plugin.Tacintern.genv = env } ~intern_env t =
  let sigma = Evd.from_env env in
  Constrintern.intern_gen Pretyping.IsType env sigma ~impls:intern_env ~pattern_mode:false ~ltacvars:Constrintern.empty_ltac_sign t

let intern_global_context { Ltac_plugin.Tacintern.genv = env } ~intern_env ctx =
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
  let intern_env, params = intern_global_context glob_sign ~intern_env:Constrintern.empty_internalization_env parameters in
  let glob_sign_params = push_glob_ctx params glob_sign in
  let params = List.rev params in
  let arity = intern_global_constr_ty ~intern_env glob_sign_params @@ CAst.make sort in
  let _, _, fields =
    List.fold_left (fun (gs,intern_env,acc) -> function
    | Vernacexpr.AssumExpr ({ CAst.v = name } as fn,bl,x), { Vernacexpr.rf_subclass = inst; rf_priority = pr; rf_notation = nots; rf_canonical = canon } ->
        if nots <> [] then Coq_elpi_utils.nYI "notation in record fields";
        if pr <> None then Coq_elpi_utils.nYI "priority in record fields";
        let atts = { Coq_elpi_HOAS.is_canonical = canon; is_coercion = inst <> Vernacexpr.NoInstance; name } in
        let x = if bl = [] then x else Constrexpr_ops.mkCProdN bl x in
        let intern_env, entry = intern_global_context ~intern_env gs [Constrexpr.CLocalAssum ([fn],Constrexpr.Default Glob_term.Explicit,x)] in
        let x = match entry with
          | [_,_,_,x] -> x
          | _ -> assert false in
        let gs = push_glob_ctx entry gs in
        gs, intern_env, (x, atts) :: acc
    | Vernacexpr.DefExpr _, _ -> Coq_elpi_utils.nYI "DefExpr")
        (glob_sign_params,intern_env,[]) fields in
  { name = (space, Names.Id.of_string name); arity; params; constructorname = constructor; fields = List.rev fields }

let _subst_record_decl s { name; arity; params; constructorname; fields } =
  let arity = subst_global_constr s arity in
  let fields = List.map (fun (t,att) -> subst_global_constr s t,att) fields in
  { name; arity; params; constructorname; fields }
let subst_record_decl _ _ = assert false (* command arguments are not substituted *)

let intern_indt_decl glob_sign { finiteness; name; parameters; non_uniform_parameters; arity; constructors } =
  let name, space = sep_last_qualid name in
  let name = Names.Id.of_string name in
  let indexes = match arity with
    | Some x -> x
    | None -> CAst.make Constrexpr.(CSort (Glob_term.UAnonymous {rigid=true})) in
  let intern_env, params = intern_global_context glob_sign ~intern_env:Constrintern.empty_internalization_env parameters in
  let intern_env, nuparams = intern_global_context glob_sign ~intern_env non_uniform_parameters in
  let params = List.rev params in
  let nuparams = List.rev nuparams in
  let allparams = params @ nuparams in
  let user_impls : Impargs.manual_implicits = List.map Coq_elpi_utils.manual_implicit_of_gdecl allparams in
  let glob_sign_params = push_glob_ctx allparams glob_sign in
  let arity = intern_global_constr_ty ~intern_env glob_sign_params indexes in
  let glob_sign_params_self = push_name glob_sign_params (Names.Name name) in
  let intern_env = push_inductive_in_intern_env intern_env name allparams arity user_impls in
  let constructors =
    List.map (fun (id,ty) -> id.CAst.v,
      intern_global_constr_ty glob_sign_params_self ~intern_env ty) constructors in
  { finiteness; name = (space, name); arity; params; nuparams; constructors }

let _subst_indt_decl s { finiteness; name; arity; params; nuparams; constructors } =
  let arity = subst_global_constr s arity in
  let params = List.map (subst_global_decl s) params in
  let nuparams = List.map (subst_global_decl s) nuparams in
  let constructors = List.map (fun (id,t) -> id, subst_global_constr s t) constructors in
  { finiteness; name; arity; params; nuparams; constructors }
let subst_indt_decl _ _ = assert false (* command arguments are not substituted *)

let expr_hole = CAst.make @@ Constrexpr.CHole(None,Namegen.IntroAnonymous,None)

let intern_context_decl glob_sign fields =
  let _intern_env, fields = intern_global_context ~intern_env:Constrintern.empty_internalization_env glob_sign fields in
  List.rev fields

let _subst_context_decl s l =
  let subst = subst_global_constr s in
  l |> List.map (fun (name,bk,bo,ty) -> name, bk, Option.map subst bo, subst ty)
let subst_context_decl _ _ = assert false (* command arguments are not substituted *)

let raw_decl_name_to_glob name =
  let name, space = sep_last_qualid name in
  (space, Names.Id.of_string name)

let raw_constant_decl_to_glob glob_sign ({ name; typ = (params,typ); body } : raw_constant_decl) =
  let intern_env, params = intern_global_context glob_sign ~intern_env:Constrintern.empty_internalization_env params in
  let glob_sign_params = push_glob_ctx params glob_sign in
  let params = List.rev params in
  let typ = Option.default expr_hole typ in
  let typ = intern_global_constr_ty ~intern_env glob_sign_params typ in
  let body = Option.map (intern_global_constr ~intern_env glob_sign_params) body in
  { name = raw_decl_name_to_glob name; params; typ; body }
let intern_constant_decl glob_sign (it : raw_constant_decl) = glob_sign, it

let _subst_constant_decl s { name; params; typ; body } =
  let typ = subst_global_constr s typ in
  let params = List.map (subst_global_decl s) params in
  let body = Option.map (subst_global_constr s) body in
  { name; params; typ; body }
let subst_constant_decl _ _ = assert false (* command arguments are not substituted *)

let glob_tac_arg glob_sign = function
  | Int _ as x -> glob_sign, x
  | String _ as x -> glob_sign, x
  | Term t -> glob_sign, Term (intern_tactic_constr glob_sign t)
  | LTac(ty,t) -> glob_sign, LTac (ty,fst @@ intern_tactic_constr glob_sign t)
  
let glob_arg glob_sign = function
  | Int _ as x -> x
  | String _ as x -> x
  | Term t -> Term (intern_tactic_constr glob_sign t)
  | RecordDecl t -> RecordDecl (intern_record_decl glob_sign t)
  | IndtDecl t -> IndtDecl (intern_indt_decl glob_sign t)
  | ConstantDecl t -> ConstantDecl (intern_constant_decl glob_sign t)
  | Context c -> Context (intern_context_decl glob_sign c)

let subst_arg mod_subst = function
  | Int _ as x -> x
  | String _ as x -> x
  | Term t ->
      Term (Ltac_plugin.Tacsubst.subst_glob_constr_and_expr mod_subst t)
  | RecordDecl t ->
      RecordDecl (subst_record_decl mod_subst t)
  | IndtDecl t ->
      IndtDecl (subst_indt_decl mod_subst t)
  | ConstantDecl t ->
      ConstantDecl (subst_constant_decl mod_subst t)
  | Context t ->
      Context (subst_context_decl mod_subst t)

let subst_tac_arg mod_subst = function
  | Int _ as x -> x
  | String _ as x -> x
  | Term t ->
      Term (Ltac_plugin.Tacsubst.subst_glob_constr_and_expr mod_subst t)
  | LTac(ty,t) ->
      LTac(ty,(Detyping.subst_glob_constr (Global.env()) mod_subst t))    
let subst_tac_arg_glob mod_subst = function
  | Int _ as x -> x
  | String _ as x -> x
  | Term t ->
      Term (Detyping.subst_glob_constr (Global.env()) mod_subst t)
  | LTac(ty,t) ->
      LTac(ty,(Detyping.subst_glob_constr (Global.env()) mod_subst t))    
    
let interp_arg ist env evd = function
  | Int _ as x -> x
  | String _ as x -> x
  | Term t -> Term(ist,t)
  | RecordDecl t -> (RecordDecl(ist,t))
  | IndtDecl t -> (IndtDecl(ist,t))
  | ConstantDecl t -> (ConstantDecl(ist,t))
  | Context c -> (Context(ist,c))

let interp_tac_arg return ist = function
| Int _ as x -> return x
| String _ as x -> return x
| Term t -> return @@ Term(ist,t)
| LTac(ty,v) ->
    let id =
      match DAst.get v with
      | Glob_term.GVar id -> id
      | _ -> assert false in
      return @@ LTac(ty,(ist,id))

let add_genarg tag pr_raw pr_glob pr_top glob subst interp =
  let wit = Genarg.make0 tag in
  let tag = Geninterp.Val.create tag in
  let () = Genintern.register_intern0 wit glob in
  let () = Genintern.register_subst0 wit subst in
  let () = Geninterp.register_interp0 wit (interp (fun x -> Ftactic.return @@ Geninterp.Val.Dyn (tag, x))) in
  let () = Geninterp.register_val0 wit (Some (Geninterp.Val.Base tag)) in
  Ltac_plugin.Pptactic.declare_extra_genarg_pprule wit pr_raw pr_glob pr_top;
  wit
;;

let wit_elpi_ftactic_arg = add_genarg "elpi_ftactic_arg"
  (fun env sigma _ _ _ -> pp_raw_tac_arg env sigma)
  (fun env sigma _ _ _ -> pp_glob_tac_arg env sigma)
  (fun env sigma _ _ _ -> pp_top_tac_arg env sigma)
  glob_tac_arg
  subst_tac_arg
  interp_tac_arg



let grecord2lp ~depth state { name; arity; params; constructorname; fields } =
  let open Coq_elpi_glob_quotation in
  let state, r = do_params params (do_record ~name ~constructorname arity fields) ~depth state in
  state, r

let contract_params env sigma name params t =
  let open Glob_term in
  let loc = Option.map Coq_elpi_utils.of_coq_loc t.CAst.loc in
  let rec contract params args =
    match params, args with
    | [], rest -> rest
    | _ :: _, [] ->
       Coq_elpi_utils.err ?loc Pp.(str "Inductive type "++ Names.Id.print name ++
         str" is not applied to enough parameters. Missing: " ++
         prlist_with_sep spc Names.Name.print (List.map (fun (x,_,_,_) -> x) params))
    | (Name.Anonymous,_,_,_) :: ps , _ :: rest -> contract ps rest
    | (Name.Name pname,_,_,_) :: ps , arg :: rest ->
       begin match DAst.get arg with
       | GVar v when Names.Id.equal pname v -> contract ps rest
       | GHole _ -> contract ps rest
       | _ -> Coq_elpi_utils.err ?loc Pp.(str "Inductive type "++ Names.Id.print name ++
                str" is not applied to parameter " ++ Names.Id.print pname ++
                str" but rather " ++ Printer.pr_glob_constr_env env sigma arg)
       end
    in
  let rec aux x =
    match DAst.get x with
    | GApp(hd,args) ->
        begin match DAst.get hd with
        | GVar id when Names.Id.equal id name ->
            DAst.make @@ GApp(hd,contract params args)
        | _ -> Glob_ops.map_glob_constr aux x
        end
    | _ -> Glob_ops.map_glob_constr aux x in
  aux t

let ginductive2lp ~depth state { finiteness; name; arity; params; nuparams; constructors } =
  let open Coq_elpi_glob_quotation in
  let space, indt_name = name in
  let contract state x = contract_params (get_global_env state) (get_sigma state) indt_name params x in
  let do_constructor ~depth state (name, ty) =
    let state, ty = do_params nuparams (do_arity (contract state ty)) ~depth state in
    state, in_elpi_indtdecl_constructor (Name.Name name) ty
  in
  let do_inductive ~depth state =
    let short_name = Name.Name indt_name in
    let qindt_name = Id.of_string_soft @@ String.concat "." (space @ [Id.to_string indt_name]) in
    let state, term_arity = gterm2lp ~depth state (Coq_elpi_utils.mk_gforall arity nuparams) in
    let state, arity = do_params nuparams (do_arity arity) ~depth state in
    under_ctx short_name term_arity None (fun ~depth state ->
      let state, constructors = Coq_elpi_utils.list_map_acc (do_constructor ~depth ) state constructors in
      state, in_elpi_indtdecl_inductive state finiteness (Name.Name qindt_name) arity constructors)
    ~depth state
  in
  let state, r = do_params params do_inductive ~depth state in
  state, r

let option_map_acc f s = function
  | None -> s, None
  | Some x ->
      let s, x = f s x in
      s, Some x
let option_map_acc2 f s = function
  | None -> s, None, []
  | Some x ->
      let s, x, gl = f s x in
      s, Some x, gl

let in_option = Elpi.(Builtin.option API.BuiltInData.any).API.Conversion.embed

let decl_name2lp name =
  let space, constant_name = name in
  let qconstant_name =
    Id.of_string_soft @@ String.concat "." (space @ [Id.to_string constant_name]) in
  in_elpi_id (Name.Name qconstant_name)

let cdecl2lp ~depth state { name; params; typ; body } =
  let open Coq_elpi_glob_quotation in
  let state, typ = do_params params (do_arity typ) ~depth state in
  let state, body = option_map_acc (fun state bo -> gterm2lp ~depth state @@ Coq_elpi_utils.mk_gfun bo params) state body in
  state, decl_name2lp name, typ, body

let ctxitemc = E.Constants.declare_global_symbol "context-item"
let ctxendc =  E.Constants.declare_global_symbol "context-end"

let rec do_context fields ~depth state =
  match fields with
  | [] -> state, E.mkGlobal ctxendc
  | (name,bk,bo,ty) :: fields ->
      let open Coq_elpi_glob_quotation in
      let state, ty = gterm2lp ~depth state ty in
      let state, bo = option_map_acc (gterm2lp ~depth) state bo in
      let state, fields = under_ctx name ty bo (do_context fields) ~depth state in
      let state, bo, _ = in_option ~depth state bo in
      let state, imp = in_elpi_imp ~depth state bk in
      state, E.mkApp ctxitemc (in_elpi_id name) [imp;ty;bo;E.mkLam fields]

let strc = E.Constants.declare_global_symbol "str"
let trmc = E.Constants.declare_global_symbol "trm"
let intc = E.Constants.declare_global_symbol "int"
let ideclc = E.Constants.declare_global_symbol "indt-decl"
let cdeclc = E.Constants.declare_global_symbol "const-decl"
let ctxc = E.Constants.declare_global_symbol "ctx-decl"

let my_cast_to_string v =
  let open Ltac_plugin in
  try Taccoerce.Value.cast (Genarg.topwit Stdarg.wit_string) v
  with CErrors.UserError _ -> try
    Taccoerce.Value.cast (Genarg.topwit Stdarg.wit_ident) v |> Names.Id.to_string
  with CErrors.UserError _ ->
    raise (Taccoerce.CannotCoerceTo "a string")
let to_list v =
  let open Ltac_plugin in
  match Taccoerce.Value.to_list v with
  | None -> raise (Taccoerce.CannotCoerceTo "a list")
  | Some l -> l

type 'a constr2lp = depth:int ->
    ?calldepth:int ->
    ([> `Options] as 'a) Coq_elpi_HOAS.coq_context ->
    API.Data.constraints ->
    API.Data.state ->
    Evd.econstr ->
    API.Data.state * API.Data.term * API.Conversion.extra_goals

let in_elpi_common_arg_aux :
  type a.
  depth:int -> ?calldepth:int -> 'c coq_context -> hyp list -> Evd.evar_map -> API.State.t -> constr2lp: 'c constr2lp -> raw:bool -> (_,_,_,_,_,_,a) arg -> API.State.t * E.term list * API.Conversion.extra_goals = fun
 ~depth ?calldepth coq_ctx hyps sigma state ~constr2lp ~raw x ->
   match x with
   | String x -> state, [E.mkApp strc (CD.of_string x) []], []
   | Int x -> state, [E.mkApp intc (CD.of_int x) []], []
   | Term (ist,glob_or_expr) -> (* TOD *)
       let closure = Ltac_plugin.Tacinterp.interp_glob_closure ist coq_ctx.env sigma glob_or_expr in
       let g = Coq_elpi_utils.detype_closed_glob coq_ctx.env sigma closure in
       let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
       let state, t = Coq_elpi_glob_quotation.gterm2lp ~depth state g in
       state, [E.mkApp trmc t []], []
   | _ -> assert false
 
let rec in_elpi_ltac_arg ~depth ?calldepth coq_ctx hyps sigma state ~constr2lp ty ist v =
  let open Ltac_plugin in
  let in_elpi_arg state = in_elpi_arg_aux ~depth ?calldepth coq_ctx hyps sigma state ~constr2lp ~raw:true in
  let self ty state = in_elpi_ltac_arg ~depth ?calldepth coq_ctx hyps sigma state ~constr2lp ty ist in
  let self_list ty state l =
    try
      let state, l, gl = API.Utils.map_acc (self ty) state l in
      state, List.flatten l, gl
    with Taccoerce.CannotCoerceTo s ->
      raise (Taccoerce.CannotCoerceTo (s ^ " list")) in
  match (ty : ltac_ty) with
  | List (List _) ->
      Coq_elpi_utils.err Pp.(str"ltac_<arg>_list_list is not implemented")
  | List ty ->
      let l = to_list v in
      self_list ty state l
  | Int ->
      let n = Taccoerce.coerce_to_int v in
      in_elpi_arg state (Int n)
  | String ->
      let s = my_cast_to_string v in
      in_elpi_arg state (String s)
  | Term -> try
        let t = Taccoerce.Value.cast (Genarg.topwit Stdarg.wit_open_constr) v in
        let state, t, gls = constr2lp ~depth ?calldepth coq_ctx E.no_constraints state t in
        state, [E.mkApp trmc t []], gls
      with CErrors.UserError _ -> try
        let closure = Taccoerce.coerce_to_uconstr v in
        let g = Coq_elpi_utils.detype_closed_glob coq_ctx.env sigma closure in
        let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
        let state, t = Coq_elpi_glob_quotation.gterm2lp ~depth state g in
        state, [E.mkApp trmc t []], []
      with Taccoerce.CannotCoerceTo _ -> try
        let id = Taccoerce.coerce_to_hyp coq_ctx.env sigma v in
        let state, t, gls = constr2lp ~depth ?calldepth coq_ctx E.no_constraints state (EConstr.mkVar id) in
        state, [E.mkApp trmc t []], gls
      with Taccoerce.CannotCoerceTo _ ->
        raise (Taccoerce.CannotCoerceTo "a term")

and in_elpi_tac_arg_aux ~depth ?calldepth coq_ctx hyps sigma state ~constr2lp = function
  | LTac(ty,(ist,id)) ->
      let v = try Id.Map.find id ist.Geninterp.lfun with Not_found -> assert false in
      begin try
        in_elpi_ltac_arg ~depth ?calldepth coq_ctx hyps sigma state ~constr2lp ty ist v
      with Ltac_plugin.Taccoerce.CannotCoerceTo s ->
        let env = Some (coq_ctx.env,sigma) in
        Ltac_plugin.Taccoerce.error_ltac_variable id env v s end
  | x -> in_elpi_common_arg_aux ~depth ?calldepth coq_ctx hyps sigma state ~constr2lp ~raw:true x

and in_elpi_arg_aux ~depth ?calldepth coq_ctx hyps sigma state ~constr2lp ~raw = function
  | RecordDecl (_ist,glob_rdecl) ->
      let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
      let state, t = grecord2lp ~depth state glob_rdecl in
      state, [E.mkApp ideclc t []], []
  | IndtDecl (_ist,glob_indt) ->
      let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
      let state, t = ginductive2lp ~depth state glob_indt in
      state, [E.mkApp ideclc t []], []
  | ConstantDecl (_ist,(glob_sign,raw_cdecl)) when raw || raw_cdecl.body == None  ->
      let glob_cdecl = raw_constant_decl_to_glob glob_sign raw_cdecl in
      let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
      let state, c, typ, body = cdecl2lp ~depth state glob_cdecl in
      let state, body, _ = in_option ~depth state body in
      state, [E.mkApp cdeclc c [body;typ]], []
  | ConstantDecl (_ist,(glob_sign,{ name; typ = (bl,typ); body = Some body; red })) ->
      let env = coq_ctx.env in
      let sigma, red = option_map_acc (Ltac_plugin.Tacinterp.interp_redexp env) sigma red in
      let sigma, (body, typ), impargs =
        ComDefinition.interp_definition ~program_mode:false
          env sigma Constrintern.empty_internalization_env bl red body typ
      in
      let state, gls0 = set_current_sigma ~depth state sigma in
      let typ =
        match typ with
        | Some x -> x
        | None -> Retyping.get_type_of env sigma body in
      let state, typ, gls1 = constr2lp ~depth ?calldepth coq_ctx E.no_constraints state typ in
      let state, typ =
        let rec aux ~depth state typ bl =
          match bl with
          | Constrexpr.CLocalAssum(x :: y :: more,k,e)::bl ->
              aux ~depth state typ (Constrexpr.CLocalAssum([x],k,e) :: Constrexpr.CLocalAssum(y :: more,k,e) :: bl)
          | Constrexpr.CLocalAssum([CAst.{ v = name }],(Constrexpr.Default ik|Constrexpr.Generalized(ik,_)),_)::bl ->
              begin match Coq_elpi_HOAS.is_prod ~depth typ with
              | None -> state, in_elpi_arity typ
              | Some(ty,bo) ->
                 let state, imp = in_elpi_imp ~depth state ik in
                 let state, bo = aux ~depth:(depth+1) state bo bl in
                 state, in_elpi_parameter name ~imp ty bo
              end
          | _ -> state, in_elpi_arity typ
          in
            aux ~depth state typ bl in
      let state, body, gls2 = constr2lp ~depth ?calldepth coq_ctx E.no_constraints state body in
      let state, body, _ = in_option ~depth state (Some body) in
      let c = decl_name2lp (raw_decl_name_to_glob name) in
      state, [E.mkApp cdeclc c [body;typ]], gls0 @ gls1 @ gls2
  | Context (_ist,glob_ctx) ->
    let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
    let state, t = do_context glob_ctx ~depth state in
    state, [E.mkApp ctxc t []], []
  | x -> in_elpi_common_arg_aux ~depth ?calldepth coq_ctx hyps sigma state ~constr2lp ~raw x
    
let in_elpi_tac_arg ~depth ?calldepth coq_ctx hyps sigma state t =
  in_elpi_tac_arg_aux ~depth ?calldepth coq_ctx hyps sigma state ~constr2lp:Coq_elpi_HOAS.constr2lp t

let in_elpi_arg ~depth ?calldepth coq_ctx state ~raw arg =
  let state, args, gls =
    in_elpi_arg_aux ~depth ?calldepth coq_ctx [] (Evd.from_env coq_ctx.env) ~constr2lp:Coq_elpi_HOAS.constr2lp_closed_ground state ~raw arg in
  assert(gls = []); (* only ltac args can generate evars and hence extra goals *)
  match args with
  | [arg] -> state, arg
  | _ -> assert false (* ltac arguments are not global *)

type coq_arg = Cint of int | Cstr of string | Ctrm of EConstr.t

let in_coq_arg ~depth proof_context constraints state t =
  match E.look ~depth t with
  | E.App(c,i,[]) when c == intc ->
      begin match E.look ~depth i with
      | E.CData c when CD.is_int c -> state, Cint (CD.to_int c), []
      | _ -> raise API.Conversion.(TypeErr (TyName"argument",depth,t))
      end
  | E.App(c,s,[]) when c == strc ->
      begin match E.look ~depth s with
      | E.CData c when CD.is_string c -> state, Cstr (CD.to_string c), []
      | _ -> raise API.Conversion.(TypeErr (TyName"argument",depth,t))
      end
  | E.App(c,t,[]) when c == trmc ->
      let state, t, gls = lp2constr ~depth proof_context constraints state t in
      state, Ctrm t, gls
  | _ -> raise API.Conversion.(TypeErr (TyName"argument",depth,t))

