(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

val init : paths:string list -> unit
val exec : Ploc.t -> string -> unit
val load_files : string list -> unit
val load_string : Ploc.t -> string -> unit
val trace : string option -> unit
val trace_at : int -> int -> unit
val print : string list -> unit
val bound_steps : int -> unit

type qualified_name = string list
type prog_arg = 
  | String of string
  | Qualid of qualified_name
  | DashQualid of qualified_name
val pp_qualified_name : qualified_name -> Pp.std_ppcmds
val pp_prog_arg : prog_arg -> Pp.std_ppcmds

val set_current_program : qualified_name -> unit
val run_command : Ploc.t -> qualified_name -> prog_arg list -> unit
