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
  arity : Genintern.glob_constr_and_expr;
  constructor : Names.Id.t option;
  fields : (Names.Name.t * bool * Genintern.glob_constr_and_expr) list
}
let pr_glob_record_decl _ = Pp.str "TODO: pr_glob_record_decl"
type parsed_record_decl = Geninterp.interp_sign * glob_record_decl

type glob_constant_decl = {
  name : string list * Id.t;
  typ : Genintern.glob_constr_and_expr option;
  body : Genintern.glob_constr_and_expr option;
}
let pr_glob_constant_decl _ = Pp.str "TODO: pr_glob_constant_decl"
type parsed_constant_decl = Geninterp.interp_sign * glob_constant_decl

type arg =
 | String of string
 | Int of int
 | Term of parsed_term
 | RecordDecl of parsed_record_decl
 | ConstantDecl of parsed_constant_decl
 | Context of parsed_term

let glob_of_closure ist env sigma glob_or_expr =
  let closure = Ltac_plugin.Tacinterp.interp_glob_closure ist env sigma glob_or_expr in
  Detyping.detype_closed_glob false Id.Set.empty env sigma closure

let grecord2lp ~depth sigma state ist { name; arity; constructor; fields } =
  let open Coq_elpi_glob_quotation in
  let space, record_name = name in
  let qrecord_name =
    Id.of_string_soft @@ String.concat "." (space @ [Id.to_string record_name]) in
  let rec do_params ~depth state x = match DAst.get x with
    | Glob_term.GSort _ ->
        let state, s = gterm2lp ~depth state x in
        let state, fields = do_fields ~depth state fields in
        let constructor = match constructor with
          | None -> Name.Name (Id.of_string ("Build_" ^ Id.to_string record_name))
          | Some x -> Name.Name x in
        state, in_elpi_indtdecl_record (Name.Name qrecord_name) s constructor fields
    | Glob_term.GProd(name,_,src,tgt) ->
        let state, src = gterm2lp ~depth state src in
        let state, tgt = under_ctx name src None do_params ~depth state tgt in
        state, in_elpi_indtdecl_parameter name src tgt
    | Glob_term.GLetIn _ -> Coq_elpi_utils.nYI "defined parameters in a record declaration"
    | _ -> CErrors.user_err Pp.(str "It does not look like a record declaration")
  and do_fields ~depth state = function
    | [] -> state, in_elpi_indtdecl_endrecord ()
    | (name,coe,f) :: fields ->
        let f = glob_of_closure ist (get_global_env state) sigma f in
        let state, f = gterm2lp ~depth state f in
        let state, fields = under_ctx name f None do_fields ~depth state fields in
        state, in_elpi_indtdecl_field state coe name f fields
  in
  let arity = glob_of_closure ist (get_global_env state) sigma arity in
  let state, r = do_params ~depth state arity in
  state, r

let cdecl2lp ~depth sigma state ist { name; typ; body } =
  let open Coq_elpi_glob_quotation in
  let option_map_acc f s = function
    | None -> s, None
    | Some x ->
        let s, x = f s x in
        s, Some x in
  let space, constant_name = name in
  let qconstant_name =
    Id.of_string_soft @@ String.concat "." (space @ [Id.to_string constant_name]) in
  let typ = Option.map (glob_of_closure ist (get_global_env state) sigma) typ in
  let state, typ = option_map_acc (gterm2lp ~depth) state typ in
  let body = Option.map (glob_of_closure ist (get_global_env state) sigma) body in
  let state, body = option_map_acc (gterm2lp ~depth) state body in
  state, in_elpi_id (Name.Name qconstant_name), typ, body

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
      let g = glob_of_closure ist coq_ctx.env sigma glob_or_expr in
      let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
      let state, t = Coq_elpi_glob_quotation.gterm2lp ~depth state g in
      state, E.mkApp trmc t []
  | RecordDecl (ist,glob_rdecl) ->
      let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
      let state, t = grecord2lp ~depth sigma state ist glob_rdecl in
      state, E.mkApp ideclc t []
  | ConstantDecl (ist,glob_cdecl) ->
      let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
      let state, c, typ, body = cdecl2lp ~depth sigma state ist glob_cdecl in
      let in_option = Elpi.(Builtin.option API.BuiltInData.any).API.Conversion.embed in
      let state, body, _ = in_option ~depth state body in
      let state, typ, _ = in_option ~depth state typ in
      state, E.mkApp cdeclc c [body;typ]
  | Context (ist,glob_or_expr) ->
      let g = glob_of_closure ist coq_ctx.env sigma glob_or_expr in
      let state = Coq_elpi_glob_quotation.set_coq_ctx_hyps state (coq_ctx,hyps) in
      let state, t = Coq_elpi_glob_quotation.gterm2lp ~depth state g in
      state, E.mkApp ctxc t []

let in_elpi_global_arg ~depth coq_ctx state arg =
  in_elpi_arg ~depth coq_ctx [] (Evd.from_env coq_ctx.env) state arg



