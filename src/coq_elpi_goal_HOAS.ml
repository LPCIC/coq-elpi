(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi_API
module E = API.Extend.Data
module CD = struct
  include API.Extend.CData
  include API.Extend.Data.C
end
open Coq_elpi_HOAS
open Names

type parsed_term =
  Ltac_plugin.Tacinterp.interp_sign * Genintern.glob_constr_and_expr

type arg = String of string | Int of int | Term of parsed_term

let strc = E.Constants.from_stringc "str"
let trmc = E.Constants.from_stringc "trm"
let intc = E.Constants.from_stringc "int"

let in_elpi_arg ~depth goal_env coq2lp_ctx evd state = function
  | String x -> state, E.mkApp strc (CD.of_string x) []
  | Int x -> state, E.mkApp intc (CD.of_int x) []
  | Term (ist,glob_or_expr) ->
      let closure = Ltac_plugin.Tacinterp.interp_glob_closure ist goal_env evd glob_or_expr in
      let g = Detyping.detype_closed_glob false Id.Set.empty goal_env evd closure in
      let state =
        Coq_elpi_glob_quotation.set_glob_ctx state coq2lp_ctx in
      let state, t =
        Coq_elpi_glob_quotation.gterm2lp ~depth state g in
      state, E.mkApp trmc t []

let in_elpi_global_arg ~depth global_env state arg =
  in_elpi_arg ~depth global_env empty_coq2lp_ctx
    (Evd.from_env global_env) state arg



