(* rocq-elpi: Coq terms as the object language of elpi                       *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

type aaction = ARm | AAdd | ASet | ANone | AAll

val set_solver_mode : aaction -> string list -> Libnames.qualid list -> unit
val solver_register : Elpi_plugin.Rocq_elpi_utils.qualified_name -> unit
val solver_activate : Elpi_plugin.Rocq_elpi_utils.qualified_name -> unit
val solver_deactivate : Elpi_plugin.Rocq_elpi_utils.qualified_name -> unit
