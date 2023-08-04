(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
module E = API.RawData
module CD = API.RawOpaqueData

open Coq_elpi_utils
open Coq_elpi_HOAS
open Names

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

module Cmd = struct

type raw_term = Constrexpr.constr_expr
type glob_term = Genintern.glob_constr_and_expr
type top_term =
  Ltac_plugin.Tacinterp.interp_sign * Genintern.glob_constr_and_expr

type raw_record_decl = Vernacentries.Preprocessed_Mind_decl.record
type glob_record_decl = Genintern.glob_sign * raw_record_decl
type top_record_decl = Geninterp.interp_sign * glob_record_decl

type raw_indt_decl = Vernacentries.Preprocessed_Mind_decl.inductive
type glob_indt_decl = Genintern.glob_sign * raw_indt_decl
type top_indt_decl = Geninterp.interp_sign * glob_indt_decl

type univpoly = Mono | Poly | CumulPoly

type raw_record_decl_elpi = {
  name : qualified_name;
  parameters : Constrexpr.local_binder_expr list;
  sort : Constrexpr.sort_expr option;
  constructor : Names.Id.t option;
  fields : (Vernacexpr.local_decl_expr * Vernacexpr.record_field_attr) list;
  univpoly : univpoly;
} 
type glob_record_decl_elpi = {
  name : string list * Names.Id.t;
  constructorname : Names.Id.t option;
  params : Glob_term.glob_decl list;
  arity : Glob_term.glob_constr;
  fields : (Glob_term.glob_constr * Coq_elpi_HOAS.record_field_spec) list;
  univpoly : univpoly;
}

let pr_raw_record_decl _ _ _ = Pp.str "TODO: pr_raw_record_decl"
let pr_glob_record_decl _ _ _ = Pp.str "TODO: pr_glob_record_decl"
let pr_top_record_decl _ _ _ = Pp.str "TODO: pr_top_record_decl"

type raw_indt_decl_elpi = {
  finiteness : Declarations.recursivity_kind;
  name : qualified_name;
  parameters : Constrexpr.local_binder_expr list;
  non_uniform_parameters : Constrexpr.local_binder_expr list option;
  arity : Constrexpr.constr_expr option;
  constructors : (Names.lident * Constrexpr.constr_expr) list;
  univpoly : univpoly;
}
type glob_indt_decl_elpi = {
  finiteness : Declarations.recursivity_kind;
  name : string list * Names.Id.t;
  arity : Glob_term.glob_constr;
  params : Glob_term.glob_decl list;
  nuparams : Glob_term.glob_decl list;
  nuparams_given : bool;
  constructors : (Names.Id.t * Glob_term.glob_constr) list;
  univpoly : univpoly;
}

let pr_raw_indt_decl _ _ _ = Pp.str "TODO: pr_raw_indt_decl"
let pr_glob_indt_decl _ _ _ = Pp.str "TODO: pr_glob_indt_decl"
let pr_top_indt_decl _ _ _ = Pp.str "TODO: pr_top_indt_decl"

type raw_constant_decl = {
  name : qualified_name;
  atts : Attributes.vernac_flags;
  udecl : Constrexpr.universe_decl_expr option;
  typ : Constrexpr.local_binder_expr list * Constrexpr.constr_expr option;
  body : Constrexpr.constr_expr option;
  red : Genredexpr.raw_red_expr option;
}
type glob_constant_decl_elpi = {
  name : string list * Names.Id.t;
  udecl : universe_decl_option;
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
type glob_context_decl = Genintern.glob_sign * raw_context_decl
type top_context_decl = Geninterp.interp_sign * glob_context_decl

let pr_raw_context_decl _ _ _ = Pp.str "TODO: pr_raw_context_decl"
let pr_glob_context_decl _ _ _ = Pp.str "TODO: pr_glob_context_decl"
let pr_top_context_decl _ _ _ = Pp.str "TODO: pr_top_context_decl"

type ('a,'b,'c,'d,'e) t =
  | Int : int            -> ('a,'b,'c,'d,'e) t
  | String : string      -> ('a,'b,'c,'d,'e) t
  | Term : 'a            -> ('a,'b,'c,'d,'e) t
  | RecordDecl : 'b      -> ('a,'b,'c,'d,'e) t
  | IndtDecl : 'c        -> ('a,'b,'c,'d,'e) t
  | ConstantDecl : 'd    -> ('a,'b,'c,'d,'e) t
  | Context : 'e         -> ('a,'b,'c,'d,'e) t

type raw  = (raw_term,  raw_record_decl,  raw_indt_decl,  raw_constant_decl,  raw_context_decl)  t
type glob = (glob_term, glob_record_decl, glob_indt_decl, glob_constant_decl, glob_context_decl) t
type top  = (top_term,  top_record_decl,  top_indt_decl,  top_constant_decl,  top_context_decl)  t

let pr_arg f g h i j x = match x with
| Int n -> Pp.int n
| String s -> Pp.qstring s
| Term s -> f s
| RecordDecl s -> g s
| IndtDecl s -> h s
| ConstantDecl s -> i s
| Context c -> j c

let pp_raw env sigma : raw -> Pp.t =
  pr_arg
    (Ppconstr.pr_constr_expr env sigma)
    (pr_raw_record_decl env sigma)
    (pr_raw_indt_decl env sigma)
    (pr_raw_constant_decl env sigma)
    (pr_raw_context_decl env sigma)

let pr_glob_constr_and_expr env sigma = function
  | (_, Some c) ->
    Ppconstr.pr_constr_expr env sigma c
  | (c, None) ->
    Printer.pr_glob_constr_env env sigma c

let pp_glob env sigma : glob -> Pp.t =
  pr_arg
    (pr_glob_constr_and_expr env sigma)
    (pr_glob_record_decl env sigma)
    (pr_glob_indt_decl env sigma)
    (pr_glob_constant_decl env sigma)
    (pr_glob_context_decl env sigma)
    
let pp_top env sigma : top -> Pp.t =
  pr_arg
    (fun (_,x) -> pr_glob_constr_and_expr env sigma x)
    (pr_top_record_decl env sigma)
    (pr_top_indt_decl env sigma)
    (pr_top_constant_decl env sigma)
    (pr_top_context_decl env sigma)
    
let sep_last_qualid = function
  | [] -> "_", []
  | l -> CList.sep_last l

let univpoly_of ~poly ~cumulative =
  match poly, cumulative with
  | true, true -> CumulPoly
  | true, false -> Poly
  | false, _ -> Mono

  let of_coq_inductive_definition id =
    let open Vernacentries.Preprocessed_Mind_decl in
    let { flags; typing_flags; private_ind; uniform; inductives } = id in
    if List.length inductives != 1 then nYI "mutual inductives";
    let inductive = List.hd inductives in
    let (((name),(parameters,non_uniform_parameters),arity,constructors),notations) = inductive in
    if notations != [] then CErrors.user_err Pp.(str "notations not supported");
    let name = [Names.Id.to_string name.CAst.v] in
    let constructors =
          List.map (function (Vernacexpr.(_,NoCoercion,NoInstance),c) -> c
            | _ -> CErrors.user_err Pp.(str "coercion and instance flags not supported"))
            constructors in
    let { template; udecl; cumulative; poly; finite } = flags in
    if template <> None then nYI "raw template polymorphic inductives";
    if udecl <> None then nYI "raw universe polymorphic inductives with universe declaration";
    {
      finiteness = finite;
      name;
      parameters;
      non_uniform_parameters;
      arity;
      constructors;
      univpoly = univpoly_of ~poly ~cumulative
    }
  let of_coq_record_definition id =
    let open Vernacentries.Preprocessed_Mind_decl in
    let { flags; primitive_proj; kind; records; } : record = id in
    if List.length records != 1 then nYI "mutual inductives";
    let open Record.Ast in
    let { name; is_coercion; binders : Constrexpr.local_binder_expr list; cfs; idbuild; sort; default_inhabitant_id : Names.Id.t option; } = List.hd records in
    if is_coercion = Vernacexpr.AddCoercion then CErrors.user_err Pp.(str "coercion flag not supported");
    let name = [Names.Id.to_string name.CAst.v] in
    let sort = sort |> Option.map (fun sort ->
      match sort.CAst.v with
      | Constrexpr.CSort s -> s
      | _ -> CErrors.user_err ?loc:sort.CAst.loc Pp.(str "only explicits sorts are supported")) in
    let { template; udecl; cumulative; poly; finite } = flags in
    if template <> None then nYI "raw template polymorphic inductives";
    if udecl <> None then nYI "raw universe polymorphic inductives with universe declaration";
    {
      name;
      parameters = binders;
      sort;
      constructor = Some idbuild;
      fields = cfs;
      univpoly = univpoly_of ~poly ~cumulative
    } 

let intern_record_decl glob_sign (it : raw_record_decl) = glob_sign, it

let raw_record_decl_to_glob glob_sign ({ name; sort; parameters; constructor; fields; univpoly } : raw_record_decl_elpi) : glob_record_decl_elpi =
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
    | Vernacexpr.AssumExpr ({ CAst.v = name } as fn,bl,x), { Vernacexpr.rf_coercion = inst; rf_priority = pr; rf_notation = nots; rf_canonical = canon } ->
        if nots <> [] then Coq_elpi_utils.nYI "notation in record fields";
        if pr <> None then Coq_elpi_utils.nYI "priority in record fields";
        let atts = { Coq_elpi_HOAS.is_canonical = canon; is_coercion = if inst = Vernacexpr.AddCoercion then Reversible else Off; name } in
        let x = if bl = [] then x else Constrexpr_ops.mkCProdN bl x in
        let intern_env, entry = intern_global_context ~intern_env gs [Constrexpr.CLocalAssum ([fn],Constrexpr.Default Glob_term.Explicit,x)] in
        let x = match entry with
          | [_,_,_,x] -> x
          | _ -> assert false in
        let gs = push_glob_ctx entry gs in
        gs, intern_env, (x, atts) :: acc
    | Vernacexpr.DefExpr _, _ -> Coq_elpi_utils.nYI "DefExpr")
        (glob_sign_params,intern_env,[]) fields in
  { name = (space, Names.Id.of_string name); arity; params; constructorname = constructor; fields = List.rev fields; univpoly }

let raw_indt_decl_to_glob glob_sign ({ finiteness; name; parameters; non_uniform_parameters; arity; constructors; univpoly } : raw_indt_decl_elpi) : glob_indt_decl_elpi =
  let name, space = sep_last_qualid name in
  let name = Names.Id.of_string name in
  let indexes = match arity with
    | Some x -> x
    | None -> CAst.make Constrexpr.(CSort (Glob_term.UAnonymous {rigid=true})) in
  let intern_env, params = intern_global_context glob_sign ~intern_env:Constrintern.empty_internalization_env parameters in
  let nuparams_given, nuparams =
    match non_uniform_parameters with
    | Some l -> true, l
    | None -> false, [] in
  let intern_env, nuparams = intern_global_context glob_sign ~intern_env nuparams in
  let params = List.rev params in
  let nuparams = List.rev nuparams in
  let allparams = params @ nuparams in
  let user_impls : Impargs.manual_implicits =
    if nuparams_given then List.map Coq_elpi_utils.manual_implicit_of_gdecl nuparams
    else List.map Coq_elpi_utils.manual_implicit_of_gdecl allparams in
  let glob_sign_params = push_glob_ctx allparams glob_sign in
  let arity = intern_global_constr_ty ~intern_env glob_sign_params indexes in
  let glob_sign_params_self = push_name glob_sign_params (Names.Name name) in
  let intern_env = push_inductive_in_intern_env intern_env name allparams arity user_impls in
  let constructors =
    List.map (fun (id,ty) -> id.CAst.v,
      intern_global_constr_ty glob_sign_params_self ~intern_env ty) constructors in
  { finiteness; name = (space, name); arity; params; nuparams; nuparams_given; constructors; univpoly }
let intern_indt_decl glob_sign (it : raw_indt_decl) = glob_sign, it

let expr_hole = CAst.make @@ Constrexpr.CHole(None,Namegen.IntroAnonymous)

let raw_context_decl_to_glob glob_sign fields =
  let _intern_env, fields = intern_global_context ~intern_env:Constrintern.empty_internalization_env glob_sign fields in
  List.rev fields
let intern_context_decl glob_sign (it : raw_context_decl) = glob_sign, it

let raw_decl_name_to_glob name =
  let name, space = sep_last_qualid name in
  (space, Names.Id.of_string name)

let raw_constant_decl_to_constr ~depth coq_ctx state { name; typ = (bl,typ); body; red; udecl; atts } =
  let env = coq_ctx.env in
  let poly =
    let open Attributes in
    parse polymorphic atts in
  let state, udecl =
    match udecl, poly with
    | None, false -> state, NotUniversePolymorphic
    | Some _, false -> nYI "only universe polymorphic definitions can take universe binders"
    | None, true -> state, NonCumulative (([],true),(Univ.Constraints.empty,true))
    | Some udecl, true ->
        let open UState in
        let sigma,  { univdecl_extensible_instance; univdecl_extensible_constraints; univdecl_constraints; univdecl_instance} =
          Constrintern.interp_univ_decl_opt (Coq_elpi_HOAS.get_global_env state) (Some udecl) in
        let ustate = Evd.evar_universe_context sigma in
        let state = merge_universe_context state ustate in
        state, NonCumulative ((univdecl_instance,univdecl_extensible_instance),(univdecl_constraints,univdecl_extensible_constraints)) in
  let sigma = get_sigma state in
  match body, typ with
  | Some body, _ ->
      let sigma, red = option_map_acc (Ltac_plugin.Tacinterp.interp_redexp env) sigma red in
      let sigma, (body, typ), impargs =
        ComDefinition.interp_definition ~program_mode:false
          env sigma Constrintern.empty_internalization_env bl red body typ
      in
      let state, gls0 = set_current_sigma ~depth state sigma in
      let typ = option_default (fun () -> Retyping.get_type_of env sigma body) typ in
      state, udecl, typ, Some body, gls0 
  | None, Some typ ->
      assert(red = None);
      let sigma, typ, impargs =
        ComAssumption.interp_assumption ~program_mode:false
          env sigma Constrintern.empty_internalization_env bl typ in
      let state, gls0 = set_current_sigma ~depth state sigma in
      state, udecl, typ, None, gls0
  | _ -> assert false


let raw_constant_decl_to_glob glob_sign ({ name; atts; udecl; typ = (params,typ); body } : raw_constant_decl) state =
  let intern_env, params = intern_global_context glob_sign ~intern_env:Constrintern.empty_internalization_env params in
  let glob_sign_params = push_glob_ctx params glob_sign in
  let params = List.rev params in
  let typ = Option.default expr_hole typ in
  let typ = intern_global_constr_ty ~intern_env glob_sign_params typ in
  let body = Option.map (intern_global_constr ~intern_env glob_sign_params) body in
  let poly =
    let open Attributes in
    parse polymorphic atts in
  let state, udecl =
    match udecl, poly with
    | None, false -> state, NotUniversePolymorphic
    | Some _, false -> nYI "only universe polymorphic definitions can take universe binders"
    | None, true -> state, NonCumulative (([],true),(Univ.Constraints.empty,true))
    | Some udecl, true ->
        let open UState in
        let sigma,  { univdecl_extensible_instance; univdecl_extensible_constraints; univdecl_constraints; univdecl_instance} =
          Constrintern.interp_univ_decl_opt (Coq_elpi_HOAS.get_global_env state) (Some udecl) in
        let ustate = Evd.evar_universe_context sigma in
        let state = merge_universe_context state ustate in
        state, NonCumulative ((univdecl_instance,univdecl_extensible_instance),(univdecl_constraints,univdecl_extensible_constraints)) in
  state, { name = raw_decl_name_to_glob name; params; typ; udecl; body }
let intern_constant_decl glob_sign (it : raw_constant_decl) = glob_sign, it

let glob glob_sign : raw -> glob = function
  | Int _ as x -> x
  | String _ as x -> x
  | Term t -> Term (intern_tactic_constr glob_sign t)
  | RecordDecl t -> RecordDecl (intern_record_decl glob_sign t)
  | IndtDecl t -> IndtDecl (intern_indt_decl glob_sign t)
  | ConstantDecl t -> ConstantDecl (intern_constant_decl glob_sign t)
  | Context c -> Context (intern_context_decl glob_sign c)

let subst _mod_subst _x =
  CErrors.anomaly Pp.(str "command arguments should not be substituted")

let interp ist env evd : glob -> top = function
  | Int _ as x -> x
  | String _ as x -> x
  | Term t -> Term(ist,t)
  | RecordDecl t -> (RecordDecl(ist,t))
  | IndtDecl t -> (IndtDecl(ist,t))
  | ConstantDecl t -> (ConstantDecl(ist,t))
  | Context c -> (Context(ist,c))

end

module Tac = struct

type raw_term = Constrexpr.constr_expr
type glob_term = Genintern.glob_constr_and_expr
type top_term = Geninterp.interp_sign * Genintern.glob_constr_and_expr

type raw_ltac_term = Constrexpr.constr_expr
type glob_ltac_term = Glob_term.glob_constr
type top_ltac_term = Geninterp.interp_sign * Names.Id.t

type ltac_ty = Int | String | Term | List of ltac_ty

type ('a,'f) t =
  | Int : int            -> ('a,'f) t
  | String : string      -> ('a,'f) t
  | Term : 'a            -> ('a,'f) t
  | LTac : ltac_ty * 'f  -> ('a,'f) t

type raw = (raw_term, raw_ltac_term) t
type glob = (glob_term, glob_ltac_term) t
type top = (top_term, top_ltac_term) t
  
let pr_raw_ltac_arg _ _ _ = Pp.str "TODO: pr_raw_ltac_arg"
let pr_glob_ltac_arg _ _ _ = Pp.str "TODO: pr_glob_ltac_arg"
let pr_top_ltac_arg _ _ _ = Pp.str "TODO: pr_top_ltac_arg"

let pr_arg f k x = match x with
  | Int n -> Pp.int n
  | String s -> Pp.qstring s
  | Term s -> f s
  | LTac(_, s) -> k s

let pr_glob_constr_and_expr env sigma = function
  | (_, Some c) ->
    Ppconstr.pr_constr_expr env sigma c
  | (c, None) ->
    Printer.pr_glob_constr_env env sigma c

let _pr_glob_constr = Printer.pr_glob_constr_env

let pp_raw env sigma : raw -> Pp.t =
  pr_arg
    (Ppconstr.pr_constr_expr env sigma)
    (pr_raw_ltac_arg env sigma)
    
let pp_glob env sigma =
  pr_arg
    (pr_glob_constr_and_expr env sigma)
    (pr_glob_ltac_arg env sigma)

let pp_top env sigma : top -> Pp.t =
  pr_arg
    ((fun (_,x) -> pr_glob_constr_and_expr env sigma x))
    (pr_top_ltac_arg env sigma)
      
let glob glob_sign : raw -> _ * glob = function
  | Int _ as x -> glob_sign, x
  | String _ as x -> glob_sign, x
  | Term t -> glob_sign, Term (intern_tactic_constr glob_sign t)
  | LTac(ty,t) -> glob_sign, LTac (ty,fst @@ intern_tactic_constr glob_sign t)

let subst mod_subst = function
  | Int _ as x -> x
  | String _ as x -> x
  | Term t ->
      Term (Ltac_plugin.Tacsubst.subst_glob_constr_and_expr mod_subst t)
  | LTac(ty,t) ->
      LTac(ty,(Detyping.subst_glob_constr (Global.env()) mod_subst t))        

let interp return ist = function
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

let wit = add_genarg "elpi_ftactic_arg"
  (fun env sigma _ _ _ -> pp_raw env sigma)
  (fun env sigma _ _ _ -> pp_glob env sigma)
  (fun env sigma _ _ _ -> pp_top env sigma)
  glob
  subst
  interp        

end

let mk_indt_decl state univpoly r =
  match univpoly with
  | Cmd.Mono -> state, E.mkApp ideclc r []
  | Cmd.Poly -> 
      let state, up, gls = universe_decl.API.Conversion.embed ~depth:0 state (([],true),(Univ.Constraints.empty,true)) in
      assert(gls=[]);
      state, E.mkApp uideclc r [up]
  | Cmd.CumulPoly ->
      let state, up, gls = universe_decl_cumul.API.Conversion.embed ~depth:0 state (([],true),(Univ.Constraints.empty,true)) in
      assert(gls=[]);
      state, E.mkApp uideclc r [up]

let grecord2lp ~depth state { Cmd.name; arity; params; constructorname; fields; univpoly } =
  let open Coq_elpi_glob_quotation in
  let state, r = do_params params (do_record ~name ~constructorname arity fields) ~depth state in
  mk_indt_decl state univpoly r
  
let contract_params env sigma name params nuparams_given t =
  if nuparams_given then t else
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

let nogls f ~depth state =
  let state, x = f ~depth state in
  state, x, ()
  
let drop_unit f ~depth state =
  let state, x, () = f ~depth state in
  state, x
  

let ginductive2lp ~depth state { Cmd.finiteness; name; arity; params; nuparams; nuparams_given; constructors; univpoly } =
  let open Coq_elpi_glob_quotation in
  let space, indt_name = name in
  let contract state x = contract_params (get_global_env state) (get_sigma state) indt_name params nuparams_given x in
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
      state, in_elpi_indtdecl_inductive state finiteness (Name.Name qindt_name) arity constructors, ())
    ~depth state
  in
  let state, r = do_params params (drop_unit do_inductive) ~depth state in
  mk_indt_decl state univpoly r

let in_option = Elpi.(Builtin.option API.BuiltInData.any).API.Conversion.embed

let decl_name2lp name =
  let space, constant_name = name in
  let qconstant_name =
    Id.of_string_soft @@ String.concat "." (space @ [Id.to_string constant_name]) in
  in_elpi_id (Name.Name qconstant_name)

let cdeclc = E.Constants.declare_global_symbol "const-decl"
let ucdeclc = E.Constants.declare_global_symbol "upoly-const-decl"

let cdecl2lp ~depth state { Cmd.name; params; typ; body; udecl } =
  let open Coq_elpi_glob_quotation in
  let state, typ = do_params params (do_arity typ) ~depth state in
  let state, body = option_map_acc (fun state bo -> gterm2lp ~depth state @@ Coq_elpi_utils.mk_gfun bo params) state body in
  let name = decl_name2lp name in
  let state, body, gls = in_option ~depth state body in
  match udecl with
  | NotUniversePolymorphic -> state, E.mkApp cdeclc name [body;typ], gls
  | Cumulative _ -> assert false
  | NonCumulative ud ->
      let state, ud, gls1 = universe_decl.API.Conversion.embed ~depth state ud in
      state, E.mkApp ucdeclc name [body;typ;ud], gls @ gls1

let ctxitemc = E.Constants.declare_global_symbol "context-item"
let ctxendc =  E.Constants.declare_global_symbol "context-end"

let rec do_context_glob fields ~depth state =
  match fields with
  | [] -> state, E.mkGlobal ctxendc
  | (name,bk,bo,ty) :: fields ->
      let open Coq_elpi_glob_quotation in
      let state, ty = gterm2lp ~depth state ty in
      let state, bo = option_map_acc (gterm2lp ~depth) state bo in
      let state, fields, () = under_ctx name ty bo (nogls (do_context_glob fields)) ~depth state in
      let state, bo, _ = in_option ~depth state bo in
      let state, imp = in_elpi_imp ~depth state bk in
      state, E.mkApp ctxitemc (in_elpi_id name) [imp;ty;bo;E.mkLam fields]

let rec do_context_constr coq_ctx csts fields ~depth state =
  let map s x = constr2lp coq_ctx csts ~depth s (EConstr.of_constr x) in
  match fields with
  | [] -> state, E.mkGlobal ctxendc, []
  | (id,bo,ty,bk) :: fields ->
      let name = Name id in
      let state, ty, gl0 = map state ty in
      let state, bo, gl1 = match bo with
        | None -> state, None, []
        | Some bo -> let state, bo, gl = map state bo in state, Some bo, gl in
        (* TODO GLS *)
      let state, fields, gl2 = Coq_elpi_glob_quotation.under_ctx name ty bo (do_context_constr coq_ctx csts fields) ~depth state in
      let state, bo, gl3 = in_option ~depth state bo in
      let state, imp = in_elpi_imp ~depth state bk in
      state, E.mkApp ctxitemc (in_elpi_id name) [imp;ty;bo;E.mkLam fields], gl0 @ gl1 @ gl2 @ gl3
      

let strc = E.Constants.declare_global_symbol "str"
let trmc = E.Constants.declare_global_symbol "trm"
let intc = E.Constants.declare_global_symbol "int"
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

(* if we make coq elaborate an arity, we get a type back. here we try to
   recoved an arity to pass that to elpi *)
let best_effort_recover_arity ~depth state glob_sign typ bl =
  let _, grouped_bl = intern_global_context glob_sign ~intern_env:Constrintern.empty_internalization_env bl in
  
  let rec aux ~depth state typ gbl =
    match gbl with
    | (name,ik,_,_) :: gbl ->
      begin match Coq_elpi_HOAS.is_prod ~depth typ with
      | None -> state, in_elpi_arity typ
      | Some(ty,bo) ->
          let state, imp = in_elpi_imp ~depth state ik in
          let state, bo = aux ~depth:(depth+1) state bo gbl in
          state, in_elpi_parameter name ~imp ty bo
      end
    | _ -> state, in_elpi_arity typ
    in
      aux ~depth state typ (List.rev grouped_bl)

let in_elpi_string_arg ~depth state x = 
  state, E.mkApp strc (CD.of_string x) [], []

let in_elpi_int_arg ~depth state x =
  state, E.mkApp intc (CD.of_int x) [], []

let in_elpi_term_arg ~depth state coq_ctx hyps sigma ist glob_or_expr =
  let closure = Ltac_plugin.Tacinterp.interp_glob_closure ist coq_ctx.env sigma glob_or_expr in
  let g = Coq_elpi_utils.detype_closed_glob coq_ctx.env sigma closure in
  let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
  let state, t = Coq_elpi_glob_quotation.gterm2lp ~depth state g in
  state, E.mkApp trmc t [], []
 
let in_elpi_tac_econstr ~depth ?calldepth coq_ctx hyps sigma state x =
  let state, gls0 = set_current_sigma ~depth state sigma in
  let state, t, gls1 = Coq_elpi_HOAS.constr2lp ~depth ?calldepth coq_ctx E.no_constraints state x in
  state, [E.mkApp trmc t []], gls0 @ gls1

let in_elpi_elab_term_arg ~depth ?calldepth state coq_ctx hyps sigma ist glob_or_expr =
  let sigma, t = Ltac_plugin.Tacinterp.interp_open_constr_with_classes ist coq_ctx.env sigma glob_or_expr in
  let state, gls0 = set_current_sigma ~depth state sigma in
  let state, t, gls1 = constr2lp_closed ~depth ?calldepth coq_ctx E.no_constraints state t in
  state, E.mkApp trmc t [], gls0 @ gls1
  
let singleton (state,x,gls) = state,[x],gls
let rec in_elpi_ltac_arg ~depth ?calldepth coq_ctx hyps sigma state ty ist v =
  let open Ltac_plugin in
  let open Tac in
  let self ty state = in_elpi_ltac_arg ~depth ?calldepth coq_ctx hyps sigma state ty ist in
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
      singleton @@ in_elpi_int_arg ~depth state n
  | String ->
      let s = my_cast_to_string v in
      singleton @@ in_elpi_string_arg ~depth state s
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
        let state, t, gls = Coq_elpi_HOAS.constr2lp ~depth ?calldepth coq_ctx E.no_constraints state (EConstr.mkVar id) in
        state, [E.mkApp trmc t []], gls
      with Taccoerce.CannotCoerceTo _ ->
        raise (Taccoerce.CannotCoerceTo "a term")

let in_elpi_tac ~depth ?calldepth coq_ctx hyps sigma state x =
  let open Tac in
  match x with
  | LTac(ty,(ist,id)) ->
      let v = try Id.Map.find id ist.Geninterp.lfun with Not_found -> assert false in
      begin try
        in_elpi_ltac_arg ~depth ?calldepth coq_ctx hyps sigma state ty ist v
      with Ltac_plugin.Taccoerce.CannotCoerceTo s ->
        let env = Some (coq_ctx.env,sigma) in
        Ltac_plugin.Taccoerce.error_ltac_variable id env v s end
  | Int x -> singleton @@ in_elpi_int_arg ~depth state x
  | String x -> singleton @@ in_elpi_string_arg ~depth state x
  | Term (ist,glob_or_expr) -> singleton @@ in_elpi_term_arg ~depth state coq_ctx hyps sigma ist glob_or_expr

let handle_template_polymorphism = function
  | None -> Some false
  | Some false -> Some false
  | Some true -> err Pp.(str "#[universes(template)] is not supported")

let in_elpi_cmd ~depth ?calldepth coq_ctx state ~raw (x : Cmd.top) =
  let open Cmd in
  let hyps = [] in
  match x with
  | RecordDecl (_ist,(glob_sign,raw_rdecl)) when raw ->
      let raw_rdecl = of_coq_record_definition raw_rdecl in
      let glob_rdecl = raw_record_decl_to_glob glob_sign raw_rdecl in
      let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
      let state, t = grecord2lp ~depth state glob_rdecl in
      state, t, []
  | RecordDecl (_ist,(glob_sign,raw_rdecl)) ->
      let open Vernacentries.Preprocessed_Mind_decl in
      let { flags = { template; poly; cumulative; udecl; finite }; primitive_proj; kind; records } = raw_rdecl in
      let template = handle_template_polymorphism template in
      let e = Record.interp_structure ~template udecl kind ~cumulative ~poly ~primitive_proj finite records in
      record_entry2lp ~depth coq_ctx E.no_constraints state ~loose_udecl:(udecl = None) e
  | IndtDecl (_ist,(glob_sign,raw_indt)) when raw ->
      let raw_indt = of_coq_inductive_definition raw_indt in
      let glob_indt = raw_indt_decl_to_glob glob_sign raw_indt in
      let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
      let state, t = ginductive2lp ~depth state glob_indt in
      state, t, []
  | IndtDecl (_ist,(glob_sign,raw_indt)) -> 
      let open Vernacentries.Preprocessed_Mind_decl in
      let { flags = { template; poly; cumulative; udecl; finite }; typing_flags; uniform; private_ind; inductives } = raw_indt in
      let template = handle_template_polymorphism template in
      let e =
        match inductives with
        | [mind_w_not] ->
            ComInductive.interp_mutual_inductive ~env:coq_ctx.env
              ~template ~cumulative ~poly ~uniform ~private_ind ?typing_flags
              udecl [mind_w_not] finite
        | _ -> nYI "(HOAS) mutual inductives"
      in
      inductive_entry2lp ~depth coq_ctx E.no_constraints state ~loose_udecl:(udecl = None) e
  | ConstantDecl (_ist,(glob_sign,raw_cdecl)) when raw ->
      let state, glob_cdecl = raw_constant_decl_to_glob glob_sign raw_cdecl state in
      let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
      cdecl2lp ~depth state glob_cdecl
  | ConstantDecl (_ist,(glob_sign,({ name; typ = (bl,_) } as raw_cdecl))) ->
      let state, udecl, typ, body, gls0 =
        raw_constant_decl_to_constr ~depth coq_ctx state raw_cdecl in
      let state, typ, gls1 = constr2lp_closed ~depth ?calldepth coq_ctx E.no_constraints state typ in
      let state, body, gls2 =
        option_map_acc2 (constr2lp_closed ~depth ?calldepth coq_ctx E.no_constraints) state body in
      let state, typ = best_effort_recover_arity ~depth state glob_sign typ bl in
      let state, body, _ = in_option ~depth state body in
      let c = decl_name2lp (raw_decl_name_to_glob name) in
      begin match udecl with
      | NotUniversePolymorphic -> state, E.mkApp cdeclc c [body;typ], gls0 @ gls1 @ gls2
      | Cumulative _ -> assert false
      | NonCumulative udecl ->
          let state, ud, gls3 = universe_decl.API.Conversion.embed ~depth state udecl in
          state, E.mkApp ucdeclc c [body;typ;ud], gls0 @ gls1 @ gls2 @ gls3
      end
  | Context (_ist,(glob_sign,raw_ctx)) when raw ->
      let glob_ctx = raw_context_decl_to_glob glob_sign raw_ctx in
      let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
      let state, t = do_context_glob glob_ctx ~depth state in
      state, E.mkApp ctxc t [], []
  | Context (_ist,(glob_sign,raw_ctx)) ->
      let sigma, ctx = ComAssumption.interp_context coq_ctx.env (get_sigma state) raw_ctx in
      let state, gls0 = set_current_sigma ~depth state sigma in
      let state, t, gls1 = do_context_constr (upcast coq_ctx) E.no_constraints ctx ~depth state in
      state, E.mkApp ctxc t [], gls0 @ gls1
  | Int x -> in_elpi_int_arg ~depth state x
  | String x -> in_elpi_string_arg ~depth state x
  | Term (ist,glob_or_expr) when raw ->
      let sigma = get_sigma state in
      in_elpi_term_arg ~depth state coq_ctx hyps sigma ist glob_or_expr
  | Term (ist,glob_or_expr) ->
      let sigma = get_sigma state in
      in_elpi_elab_term_arg ~depth ?calldepth state coq_ctx hyps sigma ist glob_or_expr

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

