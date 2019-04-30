(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_API.Extend
open Data

type parsed_term =
  Ltac_plugin.Tacinterp.interp_sign * Genintern.glob_constr_and_expr

type arg = String of string | Int of int | Term of parsed_term

val in_elpi_arg : depth:int ->
           Environ.env ->
           Coq_elpi_HOAS.coq2lp_ctx ->
           Evd.evar_map ->
           Elpi_API.Extend.Compile.State.t ->
           arg -> Elpi_API.Extend.Compile.State.t * term

val in_elpi_global_arg : depth:int -> Environ.env -> Compile.State.t -> arg -> Compile.State.t * term