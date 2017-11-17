(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)


open Elpi_API.Extend.Compile
open Elpi_API.Extend.Data

val gterm2lp :
  depth:int -> State.t -> Glob_term.glob_constr -> State.t * term

(* The context used to interpret Var("x") nodes *)
val set_glob_ctx : State.t -> int Names.Id.Map.t -> State.t

(* Used for anti-quotations *)
val is_elpi_code : (Genarg.glob_generic_argument -> bool) ref
val get_elpi_code : (Genarg.glob_generic_argument -> string) ref
