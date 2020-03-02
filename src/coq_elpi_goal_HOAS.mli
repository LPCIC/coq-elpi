(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi.API.RawData

type parsed_term =
  Ltac_plugin.Tacinterp.interp_sign * Genintern.glob_constr_and_expr

type glob_record_decl = {
  name : string list * Names.Id.t;
  arity : Genintern.glob_constr_and_expr;
  constructor : Names.Id.t option;
  fields : (Genintern.glob_constr_and_expr * Coq_elpi_HOAS.record_field_spec) list
}
val pr_glob_record_decl : glob_record_decl -> Pp.t
type parsed_record_decl = Geninterp.interp_sign * glob_record_decl

type glob_constant_decl = {
  name : string list * Names.Id.t;
  typ : Genintern.glob_constr_and_expr option;
  body : Genintern.glob_constr_and_expr option;
}
val pr_glob_constant_decl : glob_constant_decl -> Pp.t
type parsed_constant_decl = Geninterp.interp_sign * glob_constant_decl

type glob_context_decl = (Names.Name.t * Genintern.glob_constr_and_expr * Genintern.glob_constr_and_expr option) list
val pr_glob_context_decl : glob_context_decl -> Pp.t
type parsed_context_decl = Geninterp.interp_sign * glob_context_decl

type arg =
 | String of string
 | Int of int
 | Term of parsed_term
 | RecordDecl of parsed_record_decl
 | ConstantDecl of parsed_constant_decl
 | Context of parsed_context_decl

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