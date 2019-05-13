(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)


open Elpi_API
open RawData

val gterm2lp :
  depth:int -> State.t -> Glob_term.glob_constr -> State.t * term

(* The context used to interpret Var("x") nodes *)
val set_glob_ctx : State.t -> Coq_elpi_HOAS.coq2lp_ctx -> State.t

(* Used for anti-quotations *)
val is_elpi_code : (Genarg.glob_generic_argument -> bool) ref
val get_elpi_code : (Genarg.glob_generic_argument -> Elpi_API.Ast.Loc.t * string) ref
val is_elpi_code_appArg : (Genarg.glob_generic_argument -> bool) ref
val get_elpi_code_appArg : (Genarg.glob_generic_argument -> Elpi_API.Ast.Loc.t * string list) ref
