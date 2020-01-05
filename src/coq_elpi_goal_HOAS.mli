(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi.API.RawData

type parsed_term =
  Ltac_plugin.Tacinterp.interp_sign * Genintern.glob_constr_and_expr

type glob_record_decl = {
  name : Names.Id.t;
  arity : Genintern.glob_constr_and_expr;
  constructor : Names.Id.t option;
  fields : (Names.Name.t * bool * Genintern.glob_constr_and_expr) list
}
val pr_glob_record_decl : glob_record_decl -> Pp.t
type parsed_record_decl = Geninterp.interp_sign * glob_record_decl

type arg =
 | String of string
 | Int of int
 | Term of parsed_term
 | RecordDecl of parsed_record_decl

val in_elpi_arg :
  depth:int ->
  Coq_elpi_HOAS.coq_context ->
  Coq_elpi_HOAS.hyp list ->
  Evd.evar_map ->
  Elpi.API.State.t ->
  arg ->
  Elpi.API.State.t * term

val in_elpi_global_arg :
  depth:int ->
  Coq_elpi_HOAS.coq_context ->
  Elpi.API.State.t ->
  arg ->
  Elpi.API.State.t * term