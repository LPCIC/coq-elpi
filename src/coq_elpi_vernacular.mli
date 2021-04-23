(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

type qualified_name = string list
val pr_qualified_name : qualified_name -> Pp.t

type program_name = Loc.t * qualified_name

val create_program : program_name -> init:(Elpi.API.Ast.Loc.t * string) -> unit
val create_command : program_name -> unit
val create_tactic : program_name -> unit
val create_db : program_name -> init:(Elpi.API.Ast.Loc.t * string) -> unit

val typecheck_program : ?program:qualified_name -> unit -> unit

val accumulate_files  : ?program:qualified_name -> string list -> unit
val accumulate_string : ?program:qualified_name -> Elpi.API.Ast.Loc.t * string -> unit
val accumulate_db     : ?program:qualified_name -> qualified_name -> unit


val accumulate_to_db  : qualified_name -> Elpi.API.Ast.Loc.t * string -> Names.Id.t list -> scope:Coq_elpi_utils.clause_scope -> unit

val skip : atts:(Str.regexp list option * Str.regexp list option) -> ('a -> unit) -> 'a -> unit

(* Setup *)
val load_checker : string -> unit
val load_printer : string -> unit
val load_tactic : string -> unit
val load_command : string -> unit
val document_builtins : unit -> unit

(* Debug *)
val debug : string list -> unit
val trace : int -> int -> string list -> string list -> unit
val bound_steps : int -> unit
val print : qualified_name -> string list -> unit

type expr_record_decl = {
  name : qualified_name;
  parameters : Constrexpr.local_binder_expr list;
  sort : Constrexpr.sort_expr option;
  constructor : Names.Id.t option;
  fields : (Vernacexpr.local_decl_expr * Vernacexpr.record_field_attr) list
}
val pr_expr_record_decl : Environ.env -> Evd.evar_map -> expr_record_decl -> Pp.t

type expr_indt_decl = {
  finiteness : Vernacexpr.inductive_kind;
  name : qualified_name;
  parameters : Constrexpr.local_binder_expr list;
  non_uniform_parameters : Constrexpr.local_binder_expr list;
  arity : Constrexpr.constr_expr option;
  constructors : (Names.lident * Constrexpr.constr_expr) list;
}
val pr_expr_indt_decl : Environ.env -> Evd.evar_map -> expr_indt_decl -> Pp.t

type expr_constant_decl = {
  name : qualified_name;
  typ : Constrexpr.local_binder_expr list * Constrexpr.constr_expr option;
  body : Constrexpr.constr_expr option;
}
val pr_expr_constant_decl : Environ.env -> Evd.evar_map -> expr_constant_decl -> Pp.t
val pr_expr_context : Environ.env -> Evd.evar_map -> Constrexpr.local_binder_expr list -> Pp.t

type ('a,'b,'c,'d,'e) arg =
  | Int of int
  | String of string
  | Qualid of qualified_name
  | DashQualid of qualified_name
  | Term of 'a
  | RecordDecl of 'b
  | IndtDecl of 'c
  | ConstantDecl of 'd
  | Context of 'e

type raw_arg = (Constrexpr.constr_expr,  expr_record_decl, expr_indt_decl, expr_constant_decl,Constrexpr.local_binder_expr list) arg
type glob_arg = (Genintern.glob_constr_and_expr, Coq_elpi_goal_HOAS.glob_record_decl, Coq_elpi_goal_HOAS.glob_indt_decl, Coq_elpi_goal_HOAS.glob_constant_decl,Coq_elpi_goal_HOAS.glob_context_decl) arg
type parsed_arg = (Coq_elpi_goal_HOAS.parsed_term, Coq_elpi_goal_HOAS.parsed_record_decl, Coq_elpi_goal_HOAS.parsed_indt_decl, Coq_elpi_goal_HOAS.parsed_constant_decl, Coq_elpi_goal_HOAS.parsed_context_decl) arg

val pr_arg : ('a -> Pp.t) -> ('b -> Pp.t) -> ('c -> Pp.t) -> ('d -> Pp.t) -> ('e -> Pp.t) -> ('a,'b,'c,'d,'e) arg -> Pp.t
val glob_arg : Genintern.glob_sign -> raw_arg -> glob_arg
val interp_arg : Geninterp.interp_sign -> 'g Evd.sigma -> ('a,'b,'c,'d,'e) arg -> Evd.evar_map * (Geninterp.interp_sign * 'a, Geninterp.interp_sign * 'b, Geninterp.interp_sign * 'c, Geninterp.interp_sign * 'd, Geninterp.interp_sign * 'e) arg
val subst_record_decl : Mod_subst.substitution -> Coq_elpi_goal_HOAS.glob_record_decl -> Coq_elpi_goal_HOAS.glob_record_decl
val subst_indt_decl : Mod_subst.substitution -> Coq_elpi_goal_HOAS.glob_indt_decl -> Coq_elpi_goal_HOAS.glob_indt_decl
val subst_constant_decl : Mod_subst.substitution -> Coq_elpi_goal_HOAS.glob_constant_decl -> Coq_elpi_goal_HOAS.glob_constant_decl
val subst_context_decl : Mod_subst.substitution -> Coq_elpi_goal_HOAS.glob_context_decl -> Coq_elpi_goal_HOAS.glob_context_decl

val run_program : Loc.t -> qualified_name -> atts:Attributes.vernac_flags -> raw_arg list -> unit
val run_in_program : ?program:qualified_name -> Elpi.API.Ast.Loc.t * string -> unit
val run_tactic : Loc.t -> qualified_name -> Geninterp.interp_sign -> parsed_arg list -> unit Proofview.tactic
val run_in_tactic : ?program:qualified_name -> Elpi.API.Ast.Loc.t * string -> Geninterp.interp_sign -> parsed_arg list -> unit Proofview.tactic

val export_command : qualified_name -> (Loc.t,Loc.t,Loc.t) Genarg.ArgT.tag -> (raw_arg,glob_arg,parsed_arg) Genarg.ArgT.tag -> unit

