(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi.API

val coq_builtins : BuiltIn.declaration list

(* Clauses to be added to elpi programs when the execution is over *)

val clauses_for_later :
  (string list * Ast.program * Names.Id.t list * Coq_elpi_utils.clause_scope) list State.component
val set_accumulate_to_db : ((string list -> Ast.program -> Names.Id.t list -> scope:Coq_elpi_utils.clause_scope -> unit)) -> unit

type attribute_data =
  | AttributeString of string
  | AttributeLoc of Ast.Loc.t
type attribute_value =
  | AttributeEmpty
  | AttributeList of (string * attribute_value) list
  | AttributeLeaf of attribute_data

val attribute : (string * attribute_value) Conversion.t

(* In tactic mode some APIs are disabled *)
val tactic_mode : bool ref