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
val lp2constr : suspended_goal list -> CustomConstraint.t -> ?proof_ctx:proof_ctx -> depth:int -> term -> CustomConstraint.t * Constr.t

val get_env_evd : CustomConstraint.t -> Environ.env * Evd.evar_map
val get_senv_evd : CustomConstraint.t -> Safe_typing.safe_environment * Evd.evar_map
val get_current_env_evd :
  hyps -> Elpi_API.Data.solution ->
    CustomConstraint.t * Environ.env * Evd.evar_map * proof_ctx
val set_evd : CustomConstraint.t -> Evd.evar_map -> CustomConstraint.t

val tclSOLUTION2EVD : Elpi_API.Data.solution -> unit Proofview.tactic

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

val in_coq_hole : unit -> Constr.t

val in_coq_name : term -> Name.t
val is_coq_name : term -> bool

(* for quotations *)
val in_elpi_app_Arg : term -> term list -> term

(* CData relevant for other modules, e.g the one exposing Coq's API *)
val isgr : CData.t -> bool
val grout : CData.t -> Globnames.global_reference

val isuniv : CData.t -> bool
val univout : CData.t -> Univ.Universe.t
val univin : Univ.Universe.t -> CData.t

val is_sort : depth:int -> term -> bool
val is_prod : depth:int -> term -> bool
val is_globalc : constant -> bool

val isname : CData.t -> bool
val nameout : CData.t -> Name.t

val in_elpi_modpath : ty:bool -> Names.ModPath.t -> term
val is_modpath : term -> bool
val is_modtypath : term -> bool
val in_coq_modpath : term -> Names.ModPath.t

val in_elpi_module : Declarations.module_body -> term
val in_elpi_module_type : Declarations.module_type_body -> term

val new_univ : CustomConstraint.t -> CustomConstraint.t * Univ.Universe.t
val add_constraints :
  CustomConstraint.t -> Universes.universe_constraints -> CustomConstraint.t
val type_of_global : CustomConstraint.t -> Globnames.global_reference -> CustomConstraint.t * Constr.types
val normalize_univs : CustomConstraint.t -> CustomConstraint.t
val restrict_univs : CustomConstraint.t -> Univ.LSet.t -> CustomConstraint.t

val command_mode : CustomConstraint.t -> bool
val grab_global_env : CustomConstraint.t -> CustomConstraint.t

type state = Compile of Compile.State.t | Run of CustomConstraint.t

val info_of_evar : state -> Evar.t -> Constr.t * Context.Named.t * Environ.env

val in_elpi_evar_concl : Constr.t -> Evar.t -> proof_ctx -> scope:int -> (term * int) list -> depth:int -> state -> state * term * term * term
val in_elpi_evar_info : depth:int -> state -> Evar.t -> state * term
val in_elpi_ctx :
  depth:int -> state -> Context.Named.t ->
  ?mk_ctx_item:(term -> term -> term) ->
  (proof_ctx -> int Id.Map.t -> (term * int) list -> depth:int -> state -> state * term) -> state * term
val in_elpi_goal_evar_declaration : 
  hyps:term -> ev:term -> ty:term -> refined_ev:term -> term
val in_elpi_evar_declaration :
  hyps:term -> ev:term -> ty:term -> term
val in_elpi_solve :
  ?goal_name:Id.t -> hyps:term -> ev:term -> ty:term -> args:term -> term

val set_command_mode : Compile.State.t -> bool -> Compile.State.t
val set_evar_map : Compile.State.t -> Evd.evar_map -> Compile.State.t
val get_env : Compile.State.t -> Environ.env
val push_env : Compile.State.t -> Names.Name.t -> Compile.State.t
