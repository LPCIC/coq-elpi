(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi.API.RawData
open Coq_elpi_utils

type raw_term = Constrexpr.constr_expr
type glob_term = Genintern.glob_constr_and_expr
type top_term =
  Ltac_plugin.Tacinterp.interp_sign * Genintern.glob_constr_and_expr

type raw_record_decl = {
  name : qualified_name;
  parameters : Constrexpr.local_binder_expr list;
  sort : Constrexpr.sort_expr option;
  constructor : Names.Id.t option;
  fields : (Vernacexpr.local_decl_expr * Vernacexpr.record_field_attr) list
}
type glob_record_decl = {
  name : string list * Names.Id.t;
  constructorname : Names.Id.t option;
  params : Glob_term.glob_decl list;
  arity : Glob_term.glob_constr;
  fields : (Glob_term.glob_constr * Coq_elpi_HOAS.record_field_spec) list
}
type top_record_decl = Geninterp.interp_sign * glob_record_decl

type raw_indt_decl = {
  finiteness : Vernacexpr.inductive_kind;
  name : qualified_name;
  parameters : Constrexpr.local_binder_expr list;
  non_uniform_parameters : Constrexpr.local_binder_expr list;
  arity : Constrexpr.constr_expr option;
  constructors : (Names.lident * Constrexpr.constr_expr) list;
}
type glob_indt_decl = {
  finiteness : Vernacexpr.inductive_kind;
  name : string list * Names.Id.t;
  arity : Glob_term.glob_constr;
  params : Glob_term.glob_decl list;
  nuparams : Glob_term.glob_decl list;
  constructors : (Names.Id.t * Glob_term.glob_constr) list;
}
type top_indt_decl = Geninterp.interp_sign * glob_indt_decl

type raw_constant_decl = {
  name : qualified_name;
  typ : Constrexpr.local_binder_expr list * Constrexpr.constr_expr option;
  body : Constrexpr.constr_expr option;
}
val pr_raw_constant_decl : Environ.env -> Evd.evar_map -> raw_constant_decl -> Pp.t
type glob_constant_decl = {
  name : string list * Names.Id.t;
  params : Glob_term.glob_decl list;
  typ : Glob_term.glob_constr;
  body : Glob_term.glob_constr option;
}
type top_constant_decl = Geninterp.interp_sign * glob_constant_decl

type raw_context_decl = Constrexpr.local_binder_expr list
type glob_context_decl = Glob_term.glob_decl list
type top_context_decl = Geninterp.interp_sign * glob_context_decl

type raw_ltac_arg = raw_term
type glob_ltac_arg = Glob_term.glob_constr
type top_ltac_arg = Geninterp.interp_sign * Names.Id.t

type ltac_ty = Int | String | Term | List of ltac_ty

type ('a,'b,'c,'d,'e,'f) arg =
  | Int of int
  | String of string
  | Term of 'a
  | LTac of ltac_ty * 'f
  | RecordDecl of 'b
  | IndtDecl of 'c
  | ConstantDecl of 'd
  | Context of 'e

type raw_arg = (raw_term,  raw_record_decl, raw_indt_decl, raw_constant_decl,raw_context_decl,raw_term) arg
type glob_arg = (glob_term, glob_record_decl, glob_indt_decl, glob_constant_decl,glob_context_decl,Glob_term.glob_constr) arg
type top_arg = (top_term, top_record_decl, top_indt_decl, top_constant_decl, top_context_decl, top_ltac_arg) arg

val pp_raw_arg : Environ.env -> Evd.evar_map -> raw_arg -> Pp.t
val pp_glob_arg : Environ.env -> Evd.evar_map -> glob_arg -> Pp.t
val pp_top_arg : Environ.env -> Evd.evar_map -> top_arg -> Pp.t

val glob_arg : Genintern.glob_sign -> raw_arg -> glob_arg
val interp_arg : Geninterp.interp_sign -> 'g Evd.sigma -> glob_arg -> Evd.evar_map * top_arg
val subst_arg : Mod_subst.substitution -> glob_arg -> glob_arg

(* for tactics *)
val in_elpi_arg :
  depth:int -> ?calldepth:int -> 
  Coq_elpi_HOAS.full Coq_elpi_HOAS.coq_context ->
  Coq_elpi_HOAS.hyp list ->
  Evd.evar_map ->
  Elpi.API.State.t ->
  top_arg ->
  Elpi.API.State.t * term list * Elpi.API.Conversion.extra_goals

(* for commands *)
val in_elpi_global_arg :
  depth:int -> ?calldepth:int -> 
  Coq_elpi_HOAS.empty Coq_elpi_HOAS.coq_context ->
  Elpi.API.State.t ->
  top_arg ->
  Elpi.API.State.t * term

type coq_arg = Cint of int | Cstr of string | Ctrm of term

val in_coq_arg : depth:int -> Elpi.API.State.t -> term -> coq_arg
