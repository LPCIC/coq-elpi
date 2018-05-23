(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Names
open Elpi_API.Extend
open Data

type proof_ctx = Name.t list * int (* the length of the list *)

(* HOAS of terms *)
val constr2lp :
  ?proof_ctx:proof_ctx -> depth:int -> CustomConstraint.t -> Constr.t -> CustomConstraint.t * term

(* readback: adds to the evar map universes and evars in the term *)
val lp2constr : suspended_goal list -> CustomConstraint.t -> ?proof_ctx:proof_ctx -> depth:int -> term -> CustomConstraint.t * EConstr.t

val get_senv_evd : CustomConstraint.t -> Safe_typing.safe_environment * Evd.evar_map
val get_global_env_evd : CustomConstraint.t -> Environ.env * Evd.evar_map
val get_current_env_evd :
  hyps -> Elpi_API.Data.solution ->
    CustomConstraint.t * Environ.env * Evd.evar_map * proof_ctx
val set_evd : CustomConstraint.t -> Evd.evar_map -> CustomConstraint.t

val canonical_solution2lp :
  depth:int -> CustomConstraint.t ->
  ((Globnames.global_reference * Recordops.cs_pattern) * Recordops.obj_typ) ->
     CustomConstraint.t * term

val instance2lp : depth:int ->
  CustomConstraint.t -> Typeclasses.instance -> CustomConstraint.t * term

type record_field_spec = { name : string; is_coercion : bool }

val lp2inductive_entry :
  depth:int -> CustomConstraint.t -> term ->
    CustomConstraint.t * Entries.mutual_inductive_entry *
    record_field_spec list option

(* *** Low level API to reuse parts of the embedding *********************** *)
val in_elpi_gr : Globnames.global_reference -> term
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
val grout : CData.t -> Globnames.global_reference
val grin : Globnames.global_reference -> CData.t
val gref : Globnames.global_reference CData.cdata

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

val new_univ : CustomConstraint.t -> CustomConstraint.t * Univ.Universe.t
val add_constraints :
  CustomConstraint.t -> Universes.Constraints.t -> CustomConstraint.t
val type_of_global : CustomConstraint.t -> Globnames.global_reference -> CustomConstraint.t * Constr.types
val body_of_constant : CustomConstraint.t -> Names.Constant.t -> CustomConstraint.t * Constr.t option

val command_mode : CustomConstraint.t -> bool
val grab_global_env : CustomConstraint.t -> CustomConstraint.t

val cs_get_evd : CustomConstraint.t -> Evd.evar_map
val cs_set_evd : CustomConstraint.t -> Evd.evar_map -> CustomConstraint.t
val cs_get_env : CustomConstraint.t -> Environ.env
val cs_get_names_ctx : CustomConstraint.t -> Id.t list
val cs_set_ref2evk : CustomConstraint.t -> (uvar_body * Evar.t) list -> CustomConstraint.t
val cs_get_ref2evk : CustomConstraint.t -> (uvar_body * Evar.t) list

val cs_get_solution2ev : CustomConstraint.t -> Evar.t CString.Map.t
val cs_lp2constr : suspended_goal list -> CustomConstraint.t -> proof_ctx -> depth:int -> term -> CustomConstraint.t * EConstr.t
val cs_get_new_goals : CustomConstraint.t -> string option

(* Compile time *)

val cc_constr2lp : proof_ctx -> depth:int -> Compile.State.t -> Constr.t -> Compile.State.t * term

val cc_in_elpi_evar : Compile.State.t -> Evar.t -> Compile.State.t * term

val cc_mkArg :
  name_hint:string -> lvl:int -> Compile.State.t ->
    Compile.State.t * string * term

val cc_in_elpi_ctx :
  depth:int -> Compile.State.t -> Context.Named.t ->
  ?mk_ctx_item:(term -> term -> term) ->
  (proof_ctx -> int Id.Map.t -> (term * int) list -> depth:int -> Compile.State.t -> Compile.State.t * term) -> Compile.State.t * term

val cc_set_command_mode : Compile.State.t -> bool -> Compile.State.t
val cc_set_evd : Compile.State.t -> Evd.evar_map -> Compile.State.t
val cc_push_env : Compile.State.t -> Names.Name.t -> Compile.State.t
val cc_get_evd : Compile.State.t -> Evd.evar_map
val cc_get_env : Compile.State.t -> Environ.env
val cc_get_names_ctx : Compile.State.t -> Id.t list
val cc_set_new_goals : Compile.State.t -> string -> Compile.State.t

val is_unspecified_term : depth:int -> term -> bool
val in_elpi_clause : depth:int -> term -> Elpi_API.Ast.program
