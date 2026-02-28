(* rocq-elpi: Coq terms as the object language of elpi                       *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)


open Elpi.API
open RawData

val coq : Ast.Scope.language
  
(* The context used to interpret Var("x") nodes in all the APIs below *)
val set_coq_ctx_hyps : State.t -> [> `Options ] Rocq_elpi_HOAS.coq_context * hyps -> State.t

val under_ctx :
  Names.Name.t -> term -> term option ->
  k:(depth:int -> State.t -> State.t * 'b * 'c) ->
  depth:int -> State.t -> State.t * 'b * 'c

val gterm2lp :
  loc:Loc.t ->
  base:Compile.program -> 
  Glob_term.glob_constr ->
  depth:int -> State.t -> State.t * term
  val gindparams2lp :
  loc:Loc.t ->
  base:Compile.program -> 
  Glob_term.glob_decl list ->
  k:(depth:int -> State.t -> State.t * term) ->
  depth:int -> State.t -> State.t * term
val garityparams2lp :
  loc:Loc.t ->
  base:Compile.program -> 
  Glob_term.glob_decl list ->
  k:(depth:int -> State.t -> State.t * term) ->
  depth:int -> State.t -> State.t * term
val garity2lp :
  loc:Loc.t ->
  base:Compile.program -> 
  Glob_term.glob_constr ->
  depth:int -> State.t -> State.t * term
val grecord2lp :
  loc:Loc.t ->
  base:Compile.program -> 
  name:string list * Names.Id.t ->
  constructorname:Names.Id.t option ->
  Glob_term.glob_constr ->
  (Glob_term.glob_constr * Rocq_elpi_HOAS.record_field_spec) list ->
  depth:int -> State.t -> State.t * term

val runtime_gterm2lp :
  loc:Loc.t ->
  base:Compile.program -> 
  Glob_term.glob_constr ->
  depth:int -> State.t -> term
  
(* Used for anti-quotations *)
[%%if coq = "9.0" || coq = "9.1" || coq = "9.2"]
val is_elpi_code_r : (Genarg.glob_generic_argument -> bool) ref
val get_elpi_code_r : (Genarg.glob_generic_argument -> Ast.Loc.t * string) ref
val is_elpi_code_appArg_r : (Genarg.glob_generic_argument -> bool) ref
val get_elpi_code_appArg_r : (Genarg.glob_generic_argument -> Ast.Loc.t * string list) ref
[%%else]
val elpi_code_tag : ((Ast.Loc.t * string) as 'a, 'a) GenConstr.tag
val elpi_code_appArg_tag : ((Ast.Loc.t * string list) as 'a, 'a) GenConstr.tag
[%%endif]

(* Hacks *)
val mk_restricted_name : int -> string
