(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi.API.RawData

type parsed_term =
  Ltac_plugin.Tacinterp.interp_sign * Genintern.glob_constr_and_expr

type glob_record_decl = {
  name : string list * Names.Id.t;
  constructorname : Names.Id.t option;
  params : Glob_term.glob_decl list;
  arity : Glob_term.glob_constr;
  fields : (Glob_term.glob_constr * Coq_elpi_HOAS.record_field_spec) list
}
val pr_glob_record_decl : glob_record_decl -> Pp.t
type parsed_record_decl = Geninterp.interp_sign * glob_record_decl

type glob_indt_decl = {
  finiteness : Vernacexpr.inductive_kind;
  name : string list * Names.Id.t;
  arity : Glob_term.glob_constr;
  params : Glob_term.glob_decl list;
  nuparams : Glob_term.glob_decl list;
  constructors : (Names.Id.t * Glob_term.glob_constr) list;
}
val pr_glob_indt_decl : glob_indt_decl -> Pp.t
type parsed_indt_decl = Geninterp.interp_sign * glob_indt_decl

type glob_constant_decl = {
  name : string list * Names.Id.t;
  params : Glob_term.glob_decl list;
  typ : Glob_term.glob_constr;
  body : Glob_term.glob_constr option;
}
val pr_glob_constant_decl : glob_constant_decl -> Pp.t
type parsed_constant_decl = Geninterp.interp_sign * glob_constant_decl

type glob_context_decl = Glob_term.glob_decl list
val pr_glob_context_decl : glob_context_decl -> Pp.t
type parsed_context_decl = Geninterp.interp_sign * glob_context_decl

type ltac_ty = Int | String | Term | List of ltac_ty
type parsed_ltac_value = ltac_ty * Geninterp.interp_sign * Names.Id.t

type arg =
 | String of string
 | Int of int
 | Term of parsed_term
 | RecordDecl of parsed_record_decl
 | IndtDecl of parsed_indt_decl
 | ConstantDecl of parsed_constant_decl
 | Context of parsed_context_decl
 | LTac of parsed_ltac_value

val in_elpi_arg :
  depth:int -> ?calldepth:int -> 
  Coq_elpi_HOAS.full Coq_elpi_HOAS.coq_context ->
  Coq_elpi_HOAS.hyp list ->
  Evd.evar_map ->
  Elpi.API.State.t ->
  arg ->
  Elpi.API.State.t * term list * Elpi.API.Conversion.extra_goals

val in_elpi_global_arg :
  depth:int -> ?calldepth:int -> 
  Coq_elpi_HOAS.empty Coq_elpi_HOAS.coq_context ->
  Elpi.API.State.t ->
  arg ->
  Elpi.API.State.t * term

type coq_arg = Cint of int | Cstr of string | Ctrm of term

val in_coq_arg : depth:int -> Elpi.API.State.t -> term -> coq_arg
