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

val accumulate_to_db  : qualified_name -> Elpi.API.Ast.Loc.t * string -> unit

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
  arity : Constrexpr.local_binder_expr list * Glob_term.glob_sort option;
  constructor : Names.Id.t option;
  fields : Vernacexpr.local_decl_expr Vernacexpr.with_instance Vernacexpr.with_priority Vernacexpr.with_notation list
}
val pr_expr_record_decl : Environ.env -> Evd.evar_map -> expr_record_decl -> Pp.t
type ('a,'b) arg =
  | Int of int
  | String of string
  | Qualid of qualified_name
  | DashQualid of qualified_name
  | Term of 'a
  | RecordDecl of 'b

val pr_arg : ('a -> Pp.t) -> ('b -> Pp.t) -> ('a,'b) arg -> Pp.t
val glob_arg : Genintern.glob_sign -> (Constrexpr.constr_expr,  expr_record_decl) arg -> (Genintern.glob_constr_and_expr, Coq_elpi_goal_HOAS.glob_record_decl) arg
val interp_arg : Geninterp.interp_sign -> 'g Evd.sigma -> ('a,'b) arg -> Evd.evar_map * (Geninterp.interp_sign * 'a, Geninterp.interp_sign * 'b) arg
val subst_record_decl : Mod_subst.substitution -> Coq_elpi_goal_HOAS.glob_record_decl -> Coq_elpi_goal_HOAS.glob_record_decl

val run_program : Loc.t -> qualified_name -> (Constrexpr.constr_expr,expr_record_decl) arg list -> unit
val run_in_program : ?program:qualified_name -> Elpi.API.Ast.Loc.t * string -> unit
val run_tactic : Loc.t -> qualified_name -> Geninterp.interp_sign -> (Coq_elpi_goal_HOAS.parsed_term, Coq_elpi_goal_HOAS.parsed_record_decl) arg list -> unit Proofview.tactic
val run_in_tactic : ?program:qualified_name -> Elpi.API.Ast.Loc.t * string -> Geninterp.interp_sign -> (Coq_elpi_goal_HOAS.parsed_term, Coq_elpi_goal_HOAS.parsed_record_decl) arg list -> unit Proofview.tactic


