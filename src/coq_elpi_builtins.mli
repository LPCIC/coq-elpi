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

val clauses_for_later :
  (qualified_name * Ast.program * Names.Id.t list * Coq_elpi_utils.clause_scope) list State.component
val set_accumulate_to_db :
  (((qualified_name * Ast.program * Names.Id.t list * Coq_elpi_utils.clause_scope) list -> unit)) -> unit
val set_accumulate_text_to_db : ((string list -> string -> unit)) -> unit

type attribute_data =
  | AttributeString of string
  | AttributeLoc of Ast.Loc.t
type attribute_value =
  | AttributeEmpty
  | AttributeList of (string * attribute_value) list
  | AttributeLeaf of attribute_data

val attribute : (string * attribute_value) Conversion.t

(* In tactic mode some APIs are disabled *)
val tactic_mode : bool State.component

(* To dump glob, we need a quick access to the invocation site loc *)
val invocation_site_loc : Ast.Loc.t State.component

val cache_tac_abbrev : qualified_name -> unit
