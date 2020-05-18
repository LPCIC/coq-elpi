(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)


open Elpi.API
open RawData

val gterm2lp :
  depth:int -> State.t -> Glob_term.glob_constr -> State.t * term



val under_ctx :
  Names.Name.t ->
  term ->
  term option ->
  (depth:int -> State.t -> State.t * 'b) ->
  depth:int -> State.t -> State.t * 'b

val do_term :
  Glob_term.glob_constr ->
  depth:int -> State.t -> State.t * term
val do_params :
  Glob_term.glob_decl list ->
  (depth:int -> State.t -> State.t * term) ->
  depth:int -> State.t -> State.t * term
val do_arity :
  Glob_term.glob_constr ->
  depth:int -> State.t -> State.t * term

val do_record :
  name:string list * Names.Id.t ->
  constructorname:Names.Id.t option ->
  Glob_term.glob_constr ->
  (Glob_term.glob_constr * Coq_elpi_HOAS.record_field_spec) list ->
  depth:int -> State.t -> State.t * term

(* The context used to interpret Var("x") nodes *)
val set_coq_ctx_hyps : State.t -> Coq_elpi_HOAS.coq_context * Coq_elpi_HOAS.hyp list -> State.t

(* Used for anti-quotations *)
val is_elpi_code : (Genarg.glob_generic_argument -> bool) ref
val get_elpi_code : (Genarg.glob_generic_argument -> Ast.Loc.t * string) ref
val is_elpi_code_appArg : (Genarg.glob_generic_argument -> bool) ref
val get_elpi_code_appArg : (Genarg.glob_generic_argument -> Ast.Loc.t * string list) ref

(* Hacks *)
val mk_restricted_name : int -> string
