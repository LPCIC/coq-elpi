(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi.API
open Coq_elpi_utils

val coq_header_builtins : BuiltIn.declaration list
val coq_misc_builtins : BuiltIn.declaration list
val coq_locate_builtins : BuiltIn.declaration list
val coq_rest_builtins : BuiltIn.declaration list

(* Clauses to be added to elpi programs when the execution is over *)

val clauses_for_later_interp : (qualified_name * Ast.program * Names.Id.t list * Coq_elpi_utils.clause_scope) list State.component

val set_accumulate_to_db_interp : (loc:Loc.t -> (qualified_name * Ast.program * Names.Id.t list * Coq_elpi_utils.clause_scope) list -> unit) -> unit
val set_accumulate_text_to_db_interp : (loc:Loc.t -> (string list -> string -> Coq_elpi_utils.clause_scope -> unit)) -> unit

(* In tactic mode some APIs are disabled *)
val tactic_mode : bool State.component
val base : Compile.program option State.component

val cache_tac_abbrev : code:qualified_name -> name:qualified_name ->unit

