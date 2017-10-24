(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_API.Extend
open Data

type parsed_term =
  Ltac_plugin.Tacinterp.interp_sign * Tacexpr.glob_constr_and_expr

type arg = String of string | Int of int | Term of parsed_term

(* HOAS of terms, proof context, metasenv *)
val goal2query :
  Evd.evar_map -> Goal.goal -> ?main:string -> arg list -> depth:int -> Compile.State.t -> Compile.State.t * term

val tclSOLUTION2EVD : Elpi_API.Data.solution -> unit Proofview.tactic

