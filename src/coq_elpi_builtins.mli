(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi.API

val coq_builtins : BuiltIn.declaration list

(* Clauses to be added to elpi programs when the execution is over *)

val clauses_for_later :
  (string list * Ast.program * Names.Id.t list * bool) list State.component
val set_accumulate_to_db : ((string list -> Ast.program -> Names.Id.t list -> local:bool -> unit)) -> unit

val attribute : (string * Attributes.vernac_flag_value) Conversion.t

(* In tactic mode some APIs are disabled *)
val tactic_mode : bool ref