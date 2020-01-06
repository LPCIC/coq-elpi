(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Names
open Elpi.API
open Data
open RawData

(* Coq's Engine synchronization *)
type coq_context = {
  (* Elpi representation of the context *)
  section : Names.Id.t list;
  section_len : int;
  proof : EConstr.named_context;
  proof_len : int;
  local : EConstr.rel_context;
  local_len : int;

  (* Coq representation of the context *)
  env : Environ.env;

  (* Technical mappings *)
  db2name : Names.Id.t Int.Map.t;
  name2db : int Names.Id.Map.t;
  db2rel : int Int.Map.t;
  names : Id.Set.t;
}
val mk_coq_context : State.t -> coq_context

val get_current_env_sigma : depth:int ->
  Data.hyps -> constraints -> State.t -> State.t * coq_context * Evd.evar_map * Conversion.extra_goals
val set_current_sigma : depth:int -> State.t -> Evd.evar_map -> State.t * Conversion.extra_goals

(* HOAS of terms *)
val constr2lp :
  depth:int -> coq_context -> constraints -> State.t ->
  EConstr.t -> State.t * term * Conversion.extra_goals

(* readback: adds to the evar map universes and evars in the term *)
val lp2constr : 
  depth:int -> coq_context -> constraints -> State.t -> 
  term -> State.t * EConstr.t * Conversion.extra_goals

(* variants in the global context *)
val constr2lp_closed : depth:int -> constraints -> State.t ->
  EConstr.t -> State.t * term * Conversion.extra_goals
val lp2constr_closed :  depth:int -> constraints -> State.t -> 
  term -> State.t * EConstr.t * Conversion.extra_goals
val constr2lp_closed_ground : depth:int -> State.t ->
  EConstr.t -> State.t * term * Conversion.extra_goals
val lp2constr_closed_ground :  depth:int -> State.t -> 
  term -> State.t * EConstr.t * Conversion.extra_goals

val get_global_env_sigma : State.t -> Environ.env * Evd.evar_map

type record_field_spec = { name : string; is_coercion : bool }

val lp2inductive_entry :
  depth:int -> coq_context -> constraints -> State.t -> term ->
  State.t * (Entries.mutual_inductive_entry * record_field_spec list option) * Conversion.extra_goals


val get_goal_ref : depth:int -> constraints -> State.t -> term -> Evar.t option
val embed_goal : depth:int -> State.t -> Evar.t -> State.t * term * Conversion.extra_goals

(* *** Low level API to reuse parts of the embedding *********************** *)
val in_elpi_gr : depth:int -> State.t -> Names.GlobRef.t -> term
val in_elpi_sort : Sorts.t -> term
val in_elpi_flex_sort : term -> term
val in_elpi_prod : Name.t -> term -> term -> term
val in_elpi_lam : Name.t -> term -> term -> term
val in_elpi_let : Name.t -> term -> term -> term -> term
val in_elpi_appl : term -> term list -> term
val in_elpi_match : term -> term -> term list -> term
val in_elpi_fix : Name.t -> int -> term -> term -> term

val in_elpi_name : Name.t -> term

val in_coq_name : depth:int -> term -> Name.t
val is_coq_name : depth:int -> term -> bool

(* for quotations *)
val in_elpi_app_Arg : depth:int -> term -> term list -> term

type global_constant = Variable of Names.Id.t  | Constant of Names.Constant.t
val gref : Names.GlobRef.t Conversion.t
val inductive : inductive Conversion.t
val constructor : constructor Conversion.t
val constant : global_constant Conversion.t
val universe : Sorts.t Conversion.t
val global_constant_of_globref : Names.GlobRef.t -> global_constant

module GRMap : Elpi.API.Utils.Map.S with type key = Names.GlobRef.t
module GRSet : Elpi.API.Utils.Set.S with type elt = Names.GlobRef.t

(* CData relevant for other modules, e.g the one exposing Coq's API *)
val isuniv : RawOpaqueData.t -> bool
val univout : RawOpaqueData.t -> Univ.Universe.t
val univin : Univ.Universe.t -> RawOpaqueData.t
val univ : Univ.Universe.t Conversion.t

val is_sort : depth:int -> term -> bool
val is_prod : depth:int -> term -> bool

val isname : RawOpaqueData.t -> bool
val nameout : RawOpaqueData.t -> Name.t
val name : Name.t Conversion.t

val in_elpi_modpath : ty:bool -> Names.ModPath.t -> term
val is_modpath : depth:int -> term -> bool
val is_modtypath : depth:int -> term -> bool
val in_coq_modpath : depth:int -> term -> Names.ModPath.t
val modpath : Names.ModPath.t Conversion.t
val modtypath : Names.ModPath.t Conversion.t

val in_elpi_module : depth:int -> State.t -> Declarations.module_body -> GlobRef.t list
val in_elpi_module_type : Declarations.module_type_body -> string list

val new_univ : State.t -> State.t * Univ.Universe.t
val add_constraints : State.t -> UnivProblem.Set.t -> State.t
val type_of_global : State.t -> Names.GlobRef.t -> State.t * EConstr.types
val body_of_constant : State.t -> Names.Constant.t -> State.t * EConstr.t option

val command_mode : State.t -> bool
val grab_global_env : State.t -> State.t

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

(* Pushes binder for depth and its context entry (at depth+1) *)
val push_coq2lp_ctx : depth:int -> Id.t -> term -> coq2lp_ctx -> coq2lp_ctx

val mk_decl : depth:int -> Name.t -> ty:term -> term
(* Adds an Arg for the normal form with ctx_len context entry vars in scope *)

val mk_def :
  depth:int -> Name.t -> bo:term -> ty:term -> ctx_len:int -> term

(* Push a name with a dummy type (just for globalization to work) and
 * pop it back *)
val push_env : State.t -> Names.Name.t -> State.t
val pop_env : State.t -> State.t

val get_global_env : State.t -> Environ.env
val get_sigma : State.t -> Evd.evar_map

val goal2query : Environ.env ->
  Evd.evar_map -> Goal.goal -> Elpi.API.Ast.Loc.t -> ?main:string -> 'a list -> 
      in_elpi_arg:(depth:int ->
           coq_context ->
           hyp list ->
           Evd.evar_map ->
           State.t ->
           'a -> State.t * term) -> depth:int -> 
  State.t -> State.t * (Elpi.API.Ast.Loc.t * term)
val tclSOLUTION2EVD : 'a Elpi.API.Data.solution -> unit Proofview.tactic

val show_engine : State.t -> string