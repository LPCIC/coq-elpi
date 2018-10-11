(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

type qualified_name = string list
val pr_qualified_name : qualified_name -> Pp.t

val load_hoas_def : string list -> unit
val load_checker : string -> unit
val load_printer : string -> unit
val load_tactic : string -> unit
val load_command : string -> unit

val load_files : string list -> unit
val load_string : Ploc.t * string -> unit
val load_db : qualified_name -> unit
val debug : string list -> unit
val trace : int -> int -> string list -> unit
val bound_steps : int -> unit
val declare_db : qualified_name -> Ploc.t * string -> unit

type 'a arg = 
  | Int of int
  | String of string
  | Qualid of qualified_name
  | DashQualid of qualified_name
  | Term of 'a
val pr_arg : ('a -> Pp.t) -> 'a arg -> Pp.t
val glob_arg : Genintern.glob_sign -> Constrexpr.constr_expr arg -> Ltac_plugin.Tacexpr.glob_constr_and_expr arg
val interp_arg : Geninterp.interp_sign -> 'b Evd.sigma -> 'a arg -> Evd.evar_map * (Geninterp.interp_sign * 'a) arg

type program_kind = Command | Tactic

val set_current_program : ?kind:program_kind -> qualified_name -> unit

val run_program : Ploc.t * qualified_name -> Constrexpr.constr_expr arg list -> unit
val run_in_program : ?program:(Ploc.t * qualified_name) -> Ploc.t * string -> unit
val print : Ploc.t * qualified_name -> string list -> unit

val run_tactic :
  Ploc.t * qualified_name -> Geninterp.interp_sign -> Coq_elpi_goal_HOAS.parsed_term arg list -> unit Proofview.tactic
val run_in_tactic :
  ?program:(Ploc.t * qualified_name) -> Ploc.t * string -> Geninterp.interp_sign -> Coq_elpi_goal_HOAS.parsed_term arg list -> unit Proofview.tactic

val typecheck : ?program:(Ploc.t * qualified_name) -> unit -> unit
