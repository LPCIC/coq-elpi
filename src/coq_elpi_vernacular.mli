(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

val load_files : string list -> unit
val load_string : Ploc.t * string -> unit
val trace : string option -> unit
val trace_at : int -> int -> unit
val bound_steps : int -> unit

type qualified_name = string list
val pr_qualified_name : qualified_name -> Pp.std_ppcmds

module Prog : sig
  type arg = 
  | String of string
  | Qualid of qualified_name
  | DashQualid of qualified_name
  val pr_arg : arg -> Pp.std_ppcmds
end
module Tac : sig
  type 'a arg = 
  | String of string
  | Qualid of qualified_name
  | Term of 'a
  val pr_arg : ('a -> Pp.std_ppcmds) -> 'a arg -> Pp.std_ppcmds
end

type program_kind = Command | Tactic

val set_current_program : ?kind:program_kind -> qualified_name -> unit

val run_program : Ploc.t * qualified_name -> Prog.arg list -> unit
val run_in_program : ?program:(Ploc.t * qualified_name) -> Ploc.t * string -> unit
val print : Ploc.t * qualified_name -> string list -> unit

val run_tactic :
  Ploc.t * qualified_name -> Geninterp.interp_sign -> Coq_elpi_goal_HOAS.parsed_term Tac.arg list -> unit Proofview.tactic
val run_in_tactic :
  ?program:(Ploc.t * qualified_name) -> Ploc.t * string -> Geninterp.interp_sign -> Coq_elpi_goal_HOAS.parsed_term Tac.arg list -> unit Proofview.tactic
