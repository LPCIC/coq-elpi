(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
module E = API.RawData
module CD = API.RawOpaqueData

open Coq_elpi_HOAS
open Names

type parsed_term =
  Ltac_plugin.Tacinterp.interp_sign * Genintern.glob_constr_and_expr

type glob_record_decl = {
  name : string list * Id.t;
  constructorname : Names.Id.t option;
  params : Glob_term.glob_decl list;
  arity : Glob_term.glob_constr;
  fields : (Glob_term.glob_constr * record_field_spec) list
}
let pr_glob_record_decl _ = Pp.str "TODO: pr_glob_record_decl"
type parsed_record_decl = Geninterp.interp_sign * glob_record_decl

type glob_indt_decl = {
  finiteness : Vernacexpr.inductive_kind;
  name : string list * Names.Id.t;
  arity : Glob_term.glob_constr;
  params : Glob_term.glob_decl list;
  nuparams : Glob_term.glob_decl list;
  constructors : (Names.Id.t * Glob_term.glob_constr) list;
}
let pr_glob_indt_decl _ = Pp.str "TODO: pr_glob_indt_decl"
type parsed_indt_decl = Geninterp.interp_sign * glob_indt_decl


type glob_context_decl = Glob_term.glob_decl list
let pr_glob_context_decl _ = Pp.str "TODO: pr_glob_context_decl"
type parsed_context_decl = Geninterp.interp_sign * glob_context_decl

type glob_constant_decl = {
  name : string list * Id.t;
  params : Glob_term.glob_decl list;
  typ : Glob_term.glob_constr;
  body : Glob_term.glob_constr option;
}
let pr_glob_constant_decl _ = Pp.str "TODO: pr_glob_constant_decl"
type parsed_constant_decl = Geninterp.interp_sign * glob_constant_decl

type arg =
 | String of string
 | Int of int
 | Term of parsed_term
 | RecordDecl of parsed_record_decl
 | IndtDecl of parsed_indt_decl
 | ConstantDecl of parsed_constant_decl
 | Context of parsed_context_decl

let grecord2lp ~depth state { name; arity; params; constructorname; fields } =
  let open Coq_elpi_glob_quotation in
  let state, r = do_params params (do_record ~name ~constructorname arity fields) ~depth state in
  state, r

let rec list_map_acc f acc = function
  | [] -> acc, []
  | x :: xs ->
      let acc, x = f acc x in
      let acc, xs = list_map_acc f acc xs in
      acc, x :: xs

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
      let state, constructors = list_map_acc (do_constructor ~depth ) state constructors in
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
let in_option = Elpi.(Builtin.option API.BuiltInData.any).API.Conversion.embed

let cdecl2lp ~depth state { name; params; typ; body } =
  let open Coq_elpi_glob_quotation in
  let space, constant_name = name in
  let qconstant_name =
    Id.of_string_soft @@ String.concat "." (space @ [Id.to_string constant_name]) in
  let state, typ = do_params params (do_arity typ) ~depth state in
  let state, body = option_map_acc (fun state bo -> gterm2lp ~depth state @@ Coq_elpi_utils.mk_gfun bo params) state body in
  state, in_elpi_id (Name.Name qconstant_name), typ, body

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

let in_elpi_arg ~depth coq_ctx hyps sigma state = function
  | String x -> state, E.mkApp strc (CD.of_string x) []
  | Int x -> state, E.mkApp intc (CD.of_int x) []
  | Term (ist,glob_or_expr) ->
      let closure = Ltac_plugin.Tacinterp.interp_glob_closure ist coq_ctx.env sigma glob_or_expr in
      let g = Detyping.detype_closed_glob false Id.Set.empty coq_ctx.env sigma closure in
      let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
      let state, t = Coq_elpi_glob_quotation.gterm2lp ~depth state g in
      state, E.mkApp trmc t []
  | RecordDecl (_ist,glob_rdecl) ->
      let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
      let state, t = grecord2lp ~depth state glob_rdecl in
      state, E.mkApp ideclc t []
  | IndtDecl (_ist,glob_indt) ->
      let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
      let state, t = ginductive2lp ~depth state glob_indt in
      state, E.mkApp ideclc t []
  | ConstantDecl (_ist,glob_cdecl) ->
      let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
      let state, c, typ, body = cdecl2lp ~depth state glob_cdecl in
      let state, body, _ = in_option ~depth state body in
      state, E.mkApp cdeclc c [body;typ]
  | Context (_ist,glob_ctx) ->
      let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
      let state, t = do_context glob_ctx ~depth state in
      state, E.mkApp ctxc t []

let in_elpi_global_arg ~depth coq_ctx state arg =
  in_elpi_arg ~depth coq_ctx [] (Evd.from_env coq_ctx.env) state arg



