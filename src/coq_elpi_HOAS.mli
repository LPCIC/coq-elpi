(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Names
open Elpi.API
open Data
open RawData

(* Coq's Engine synchronization *)
type empty = [ `Options ]
type full  = [ `Options | `Context ]

type hole_mapping =
  | Verbatim   (* 1:1 correspondence between UVar and Evar *)
  | Heuristic  (* new UVar outside Llam is pruned before being linked to Evar *)
  | Implicit   (* No link, UVar is intepreted as a "hole" constant *)
type options = {
  hoas_holes : hole_mapping option;
  local : bool option;
  deprecation : Deprecation.t option;
  primitive : bool option;
  failsafe : bool; (* readback is resilient to illformed terms *)
  ppwidth : int;
  ppall : bool;
}

type 'a coq_context = {
  (* Elpi representation of the context *)
  section : Names.Id.t list;
  section_len : int;
  proof : EConstr.named_context;
  proof_len : int;
  local : (int * EConstr.rel_declaration) list;
  local_len : int;

  (* Coq representation of the context *)
  env : Environ.env;

  (* Technical mappings *)
  db2name : Names.Id.t Int.Map.t;
  name2db : int Names.Id.Map.t;
  db2rel : int Int.Map.t;
  names : Id.Set.t;

  (* Options (get-option context entries) *)
  options : options;
}
val mk_coq_context : options:options -> State.t -> empty coq_context
val get_options : depth:int -> Data.hyps -> State.t -> options
val default_options : options
val upcast : [> `Options ] coq_context -> full coq_context

val get_current_env_sigma : depth:int ->
  Data.hyps -> constraints -> State.t -> State.t * full coq_context * Evd.evar_map * Conversion.extra_goals
val set_current_sigma : depth:int -> State.t -> Evd.evar_map -> State.t * Conversion.extra_goals
val get_global_env_current_sigma : depth:int ->
  Data.hyps -> constraints -> State.t -> State.t * empty coq_context * Evd.evar_map * Conversion.extra_goals

(* HOAS of terms *)
val constr2lp :
  depth:int -> full coq_context -> constraints -> State.t ->
  EConstr.t -> State.t * term * Conversion.extra_goals

(* readback: adds to the evar map universes and evars in the term *)
val lp2constr :
  depth:int -> full coq_context -> constraints -> State.t -> 
  term -> State.t * EConstr.t * Conversion.extra_goals

(* variants in the global context *)
val constr2lp_closed : depth:int -> empty coq_context -> constraints -> State.t ->
  EConstr.t -> State.t * term * Conversion.extra_goals
val lp2constr_closed :  depth:int -> empty coq_context -> constraints -> State.t ->
  term -> State.t * EConstr.t * Conversion.extra_goals
val constr2lp_closed_ground : depth:int -> empty coq_context -> constraints -> State.t ->
  EConstr.t -> State.t * term * Conversion.extra_goals
val lp2constr_closed_ground :  depth:int -> empty coq_context -> constraints -> State.t ->
  term -> State.t * EConstr.t * Conversion.extra_goals

(* another variant, to call the pretyper *)
val lp2skeleton :
  depth:int -> full coq_context -> constraints -> State.t ->
  term -> State.t * Glob_term.glob_constr * Conversion.extra_goals

type record_field_spec = { name : Name.t; is_coercion : bool; is_canonical : bool }

val lp2inductive_entry :
  depth:int -> empty coq_context -> constraints -> State.t -> term ->
  State.t * (Entries.mutual_inductive_entry * (bool * record_field_spec list) option * DeclareInd.one_inductive_impls list) * Conversion.extra_goals

val inductive_decl2lp :
  depth:int -> empty coq_context -> constraints -> State.t -> ((Declarations.mutual_inductive_body * Declarations.one_inductive_body) * (Glob_term.binding_kind list * Glob_term.binding_kind list list)) ->
    State.t * term * Conversion.extra_goals

val in_elpi_id : Names.Name.t -> term
val in_elpi_bool : State.t -> bool -> term
val in_elpi_parameter : Names.Name.t -> imp:term -> term -> term -> term
val in_elpi_arity : term -> term
val in_elpi_indtdecl_record : Names.Name.t -> term -> Names.Name.t -> term -> term
val in_elpi_indtdecl_endrecord : unit -> term
val in_elpi_indtdecl_field : depth:int -> State.t -> record_field_spec -> term -> term -> State.t * term
val in_elpi_indtdecl_inductive : State.t -> Vernacexpr.inductive_kind -> Names.Name.t -> term -> term list -> term
val in_elpi_indtdecl_constructor : Names.Name.t -> term -> term

val get_goal_ref : depth:int -> constraints -> State.t -> term -> Evar.t option
val embed_goal : depth:int -> State.t -> Evar.t -> State.t * term * Conversion.extra_goals

(* *** Low level API to reuse parts of the embedding *********************** *)
type 'a unspec = Given of 'a | Unspec
val unspec : 'a Conversion.t -> 'a unspec Conversion.t
val unspecC : ('a,'b,'c) ContextualConversion.t -> ('a unspec,'b,'c) ContextualConversion.t
val unspec2opt : 'a unspec -> 'a option
val opt2unspec : 'a option -> 'a unspec

val in_elpi_gr : depth:int -> State.t -> Names.GlobRef.t -> term
val in_elpi_sort : Sorts.t -> term
val in_elpi_flex_sort : term -> term
val in_elpi_prod : Name.t -> term -> term -> term
val in_elpi_lam : Name.t -> term -> term -> term
val in_elpi_let : Name.t -> term -> term -> term -> term
val in_elpi_appl : depth:int -> term -> term list -> term
val in_elpi_match : term -> term -> term list -> term
val in_elpi_fix : Name.t -> int -> term -> term -> term
val in_elpi_uint63 : depth:int -> state -> Uint63.t -> state * term
val in_elpi_float64 : depth:int -> state -> Float64.t -> state * term

val in_elpi_name : Name.t -> term

val in_coq_name : depth:int -> term -> Name.t
val is_coq_name : depth:int -> term -> bool

val in_coq_imp : depth:int -> State.t -> term -> State.t * Glob_term.binding_kind
val in_elpi_imp : depth:int -> State.t -> Glob_term.binding_kind -> State.t * term

(* for quotations *)
val in_elpi_app_Arg : depth:int -> term -> term list -> term

type global_constant = Variable of Names.Id.t  | Constant of Names.Constant.t
val gref : Names.GlobRef.t Conversion.t
val inductive : inductive Conversion.t
val constructor : constructor Conversion.t
val constant : global_constant Conversion.t
val universe : Sorts.t Conversion.t
val global_constant_of_globref : Names.GlobRef.t -> global_constant
val abbreviation : Globnames.syndef_name Conversion.t
val implicit_kind : Glob_term.binding_kind Conversion.t

module GRMap : Elpi.API.Utils.Map.S with type key = Names.GlobRef.t
module GRSet : Elpi.API.Utils.Set.S with type elt = Names.GlobRef.t

(* CData relevant for other modules, e.g the one exposing Coq's API *)
val isuniv : RawOpaqueData.t -> bool
val univout : RawOpaqueData.t -> Univ.Universe.t
val univin : Univ.Universe.t -> term
val univ : Univ.Universe.t Conversion.t

val is_sort : depth:int -> term -> bool
val is_prod : depth:int -> term -> bool
val is_lam : depth:int -> term -> (term * term) option (* ty, bo @ depth+1 *)

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

type record_field_att =
  | Coercion of bool
  | Canonical of bool
val record_field_att : record_field_att Conversion.t

val new_univ : State.t -> State.t * Univ.Universe.t
val add_constraints : State.t -> UnivProblem.Set.t -> State.t
val type_of_global : State.t -> Names.GlobRef.t -> State.t * EConstr.types
val body_of_constant : State.t -> Names.Constant.t -> State.t * EConstr.t option

val command_mode : State.t -> bool
val grab_global_env : State.t -> State.t
val grab_global_env_drop_univs : State.t -> State.t

val mk_decl : depth:int -> Name.t -> ty:term -> term
(* Adds an Arg for the normal form with ctx_len context entry vars in scope *)

val mk_def :
  depth:int -> Name.t -> bo:term -> ty:term -> term

(* Push a name with a dummy type (just for globalization to work) and
 * pop it back *)
val push_env : State.t -> Names.Name.t -> State.t
val pop_env : State.t -> State.t

val get_global_env : State.t -> Environ.env
val get_sigma : State.t -> Evd.evar_map

type hyp = { ctx_entry : term; depth : int }

val goal2query : Environ.env ->
  Evd.evar_map -> Goal.goal -> Elpi.API.Ast.Loc.t -> ?main:string -> 'a list -> 
      in_elpi_arg:(depth:int ->
           empty coq_context ->
           hyp list ->
           Evd.evar_map ->
           State.t ->
           'a -> State.t * term) -> depth:int -> 
  State.t -> State.t * (Elpi.API.Ast.Loc.t * term)
val tclSOLUTION2EVD : 'a Elpi.API.Data.solution -> unit Proofview.tactic

val show_engine : State.t -> string