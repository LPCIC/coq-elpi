(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

type qualified_name = string list
val pr_qualified_name : qualified_name -> Pp.t

type program_name = Loc.t * qualified_name
type object_kind = Command | Tactic | Db

val create : object_kind -> program_name -> unit
val typecheck_program : ?program:qualified_name -> unit -> unit

val accumulate_files  : ?program:qualified_name -> string list -> unit
val accumulate_string : ?program:qualified_name -> Elpi.API.Ast.Loc.t * string -> unit
val accumulate_db     : ?program:qualified_name -> qualified_name -> unit

val accumulate_to_db  : qualified_name -> Elpi.API.Ast.Loc.t * string -> unit

(* Setup *)
val load_hoas_def : string list -> unit
val load_checker : string -> unit
val load_printer : string -> unit
val load_tactic : string -> unit
val load_command : string -> unit

(* Debug *)
val debug : string list -> unit
val trace : int -> int -> string list -> string list -> unit
val bound_steps : int -> unit
val print : qualified_name -> string list -> unit

type 'a arg = 
  | Int of int
  | String of string
  | Qualid of qualified_name
  | DashQualid of qualified_name
  | Term of 'a
val pr_arg : ('a -> Pp.t) -> 'a arg -> Pp.t
val glob_arg : Genintern.glob_sign -> Constrexpr.constr_expr arg -> Genintern.glob_constr_and_expr arg
val interp_arg : Geninterp.interp_sign -> 'b Evd.sigma -> 'a arg -> Evd.evar_map * (Geninterp.interp_sign * 'a) arg

val run_program : Loc.t -> qualified_name -> Constrexpr.constr_expr arg list -> unit
val run_in_program : ?program:qualified_name -> Elpi.API.Ast.Loc.t * string -> unit
val run_tactic : Loc.t -> qualified_name -> Geninterp.interp_sign -> Coq_elpi_goal_HOAS.parsed_term arg list -> unit Proofview.tactic
val run_in_tactic : ?program:qualified_name -> Elpi.API.Ast.Loc.t * string -> Geninterp.interp_sign -> Coq_elpi_goal_HOAS.parsed_term arg list -> unit Proofview.tactic


