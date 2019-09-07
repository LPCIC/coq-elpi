(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi.API
open RawData

type parsed_term =
  Ltac_plugin.Tacinterp.interp_sign * Genintern.glob_constr_and_expr

type arg = String of string | Int of int | Term of parsed_term

val in_elpi_arg : depth:int ->
           Coq_elpi_HOAS.coq_context ->
           Coq_elpi_HOAS.hyp list ->
           Evd.evar_map ->
           State.t ->
           arg -> State.t * term

val in_elpi_global_arg : depth:int -> Coq_elpi_HOAS.coq_context -> State.t -> arg -> State.t * term