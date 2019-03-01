(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Names
open Elpi_API.Extend
open Data

type coq_proof_ctx_names = Name.t list * int (* the length of the list *)

(* HOAS of terms *)
val constr2lp :
  ?coq_proof_ctx_names:coq_proof_ctx_names -> depth:int -> CustomState.t -> Constr.t -> CustomState.t * term

(* readback: adds to the evar map universes and evars in the term *)
val lp2constr : ?tolerate_undef_evar:bool -> suspended_goal list -> CustomState.t -> ?coq_proof_ctx_names:coq_proof_ctx_names -> depth:int -> term -> CustomState.t * EConstr.t

val get_global_env_evd : CustomState.t -> Environ.env * Evd.evar_map
val get_current_env_evd : depth:int ->
  hyps -> Elpi_API.Extend.Data.solution ->
    CustomState.t * Environ.env * Evd.evar_map * coq_proof_ctx_names
val set_evd : CustomState.t -> Evd.evar_map -> CustomState.t

val canonical_solution2lp :
  depth:int -> CustomState.t ->
  ((Names.GlobRef.t * Recordops.cs_pattern) * Recordops.obj_typ) ->
     CustomState.t * term

val instance2lp : depth:int ->
  CustomState.t -> Typeclasses.instance -> CustomState.t * term

type record_field_spec = { name : string; is_coercion : bool }

val lp2inductive_entry :
  depth:int -> CustomState.t -> term ->
    CustomState.t * Entries.mutual_inductive_entry *
    record_field_spec list option

(* *** Low level API to reuse parts of the embedding *********************** *)
val in_elpi_gr : Names.GlobRef.t -> term
val in_elpi_sort : Sorts.t -> term
val in_elpi_flex_sort : term -> term
val in_elpi_prod : Name.t -> term -> term -> term
val in_elpi_lam : Name.t -> term -> term -> term
val in_elpi_let : Name.t -> term -> term -> term -> term
val in_elpi_appl : term -> term list -> term
val in_elpi_match : term -> term -> term list -> term
val in_elpi_fix : Name.t -> int -> term -> term -> term

val in_elpi_implicit : term

val in_elpi_tt : term
val in_elpi_ff : term

val in_elpi_name : Name.t -> term

val in_coq_hole : unit -> EConstr.t

val in_coq_name : depth:int -> term -> Name.t
val is_coq_name : depth:int -> term -> bool

(* for quotations *)
val in_elpi_app_Arg : depth:int -> term -> term list -> term

(* CData relevant for other modules, e.g the one exposing Coq's API *)
val isgr : CData.t -> bool
val grout : CData.t -> Names.GlobRef.t
val grin : Names.GlobRef.t -> CData.t
val gref : Names.GlobRef.t CData.cdata

val isuniv : CData.t -> bool
val univout : CData.t -> Univ.Universe.t
val univin : Univ.Universe.t -> CData.t
val univ : Univ.Universe.t CData.cdata

val is_sort : depth:int -> term -> bool
val is_prod : depth:int -> term -> bool
val is_globalc : constant -> bool

val isname : CData.t -> bool
val nameout : CData.t -> Name.t
val name : Name.t CData.cdata

val in_elpi_modpath : ty:bool -> Names.ModPath.t -> term
val is_modpath : depth:int -> term -> bool
val is_modtypath : depth:int -> term -> bool
val in_coq_modpath : depth:int -> term -> Names.ModPath.t
val modpath : Names.ModPath.t CData.cdata
val modtypath : Names.ModPath.t CData.cdata

val in_elpi_module : Declarations.module_body -> term list
val in_elpi_module_type : Declarations.module_type_body -> string list

val new_univ : CustomState.t -> CustomState.t * Univ.Universe.t
val add_constraints :
  CustomState.t -> UnivProblem.Set.t -> CustomState.t
val type_of_global : CustomState.t -> Names.GlobRef.t -> CustomState.t * Constr.types
val body_of_constant : CustomState.t -> Names.Constant.t -> CustomState.t * Constr.t option

val command_mode : CustomState.t -> bool
val grab_global_env : CustomState.t -> CustomState.t

val cs_get_evd : CustomState.t -> Evd.evar_map
val cs_set_evd : CustomState.t -> Evd.evar_map -> CustomState.t
val cs_get_env : CustomState.t -> Environ.env
val cs_get_names_ctx : CustomState.t -> Id.t list
val cs_set_ref2evk : CustomState.t -> (uvar_body * Evar.t) list -> CustomState.t
val cs_get_ref2evk : CustomState.t -> (uvar_body * Evar.t) list

val cs_get_solution2ev : CustomState.t -> Evar.t CString.Map.t
val cs_lp2constr : suspended_goal list -> CustomState.t -> coq_proof_ctx_names -> depth:int -> term -> CustomState.t * EConstr.t
val cs_get_new_goals : CustomState.t -> string option

(* Compile time *)

val cc_constr2lp : coq_proof_ctx_names -> depth:int -> Compile.State.t -> Constr.t -> Compile.State.t * term

val cc_in_elpi_evar : Compile.State.t -> Evar.t -> Compile.State.t * term

val cc_mkArg :
  name_hint:string -> lvl:int -> Compile.State.t ->
    Compile.State.t * string * term

(* Maps a Coq name (bound in the context) to its De Bruijn level
 * The type (and optionally body) is given by the hyps. Each hyp is generated
 * at a depth level, and it may need to be pushed down. Cfr:
 *
 *  pi x\ decl x t => py y\ def y t b => ....
 *  pi x y\ decl x t => def y t b => ....
 *
 * Given that a priori you may not know the size of the context things are
 * generated in the first form, and eventually lifted down. *)
type hyp = { ctx_entry : term; depth : int }
type coq2lp_ctx = { coq_name2dbl : int Id.Map.t; hyps : hyp list }
val empty_coq2lp_ctx : coq2lp_ctx

val pp_coq2lp_ctx : Format.formatter -> coq2lp_ctx -> unit

val cc_in_elpi_ctx :
  depth:int -> Compile.State.t -> Constr.named_context ->
  ?mk_ctx_item:(term -> term -> term) ->
  (coq_proof_ctx_names -> coq2lp_ctx -> depth:int ->
     Compile.State.t -> Compile.State.t * term) ->
  Compile.State.t * term

(* Pushes binder for depth and its context entry (at depth+1) *)
val push_coq2lp_ctx : depth:int -> Id.t -> term -> coq2lp_ctx -> coq2lp_ctx
val mk_decl : depth:int -> Name.t -> ty:term -> term
(* Adds an Arg for the normal form with ctx_len context entry vars in scope *)
val mk_def : depth:int -> Name.t -> bo:term -> ty:term -> ctx_len:int -> Compile.State.t -> Compile.State.t * term

val cc_set_command_mode : Compile.State.t -> bool -> Compile.State.t
val cc_set_evd : Compile.State.t -> Evd.evar_map -> Compile.State.t

(* Push a name with a dummy type (just for globalization to work) and
 * pop it back *)
val cc_push_env : Compile.State.t -> Names.Name.t -> Compile.State.t
val cc_pop_env : Compile.State.t -> Compile.State.t

val cc_get_evd : Compile.State.t -> Evd.evar_map
val cc_get_env : Compile.State.t -> Environ.env
val cc_get_names_ctx : Compile.State.t -> Id.t list
val cc_set_new_goals : Compile.State.t -> string -> Compile.State.t

val is_unspecified_term : depth:int -> term -> bool
val in_elpi_clause : depth:int -> term -> Elpi_API.Ast.program
