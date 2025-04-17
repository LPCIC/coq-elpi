(* rocq-elpi: Coq terms as the object language of elpi                       *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Names
open Elpi.API
open Data
open RawData

(* Coq's Engine synchronization *)
type empty = [ `Options ]
type full  = [ `Options | `Context ]

type ppoption = All | Most | Normal
type hole_mapping =
  | Verbatim   (* 1:1 correspondence between UVar and Evar *)
  | Heuristic  (* new UVar outside Llam is pruned before being linked to Evar *)
  | Implicit   (* No link, UVar is intepreted as a "hole" constant *)
type uinstanceoption =
  | NoInstance
    (* the elpi command involved has to generate a fresh instance *)
  | ConcreteInstance of UVars.Instance.t
    (* a concrete instance was provided, the command will use it *)
  | VarInstance of (FlexibleData.Elpi.t * RawData.term list * inv_rel_key)
    (* a variable was provided, the command will compute the instance to unify with it *)

type universe_decl = (Univ.Level.t list * bool) * (Univ.Constraints.t * bool)
type universe_decl_cumul = ((Univ.Level.t * UVars.Variance.t option) list  * bool) * (Univ.Constraints.t * bool)
type universe_decl_option =
  | NotUniversePolymorphic
  | Cumulative of universe_decl_cumul
  | NonCumulative of universe_decl

type options = {
  hoas_holes : hole_mapping option;
  local : bool option;
  user_warns : UserWarn.t option;
  primitive : bool option;
  failsafe : bool; (* readback is resilient to illformed terms *)
  ppwidth : int;
  pp : ppoption;
  pplevel : Constrexpr.entry_relative_level;
  using : string option;
  inline : Declaremods.inline;
  uinstance : uinstanceoption;
  universe_decl : universe_decl_option;
  reversible : bool option;
  keepunivs : bool option;
  redflags : RedFlags.reds option;
  no_tc: bool option;
  algunivs : bool option;
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
val default_options : unit -> options
val upcast : [> `Options ] coq_context -> full coq_context

val get_current_env_sigma : depth:int ->
  Data.hyps -> constraints -> State.t -> State.t * full coq_context * Evd.evar_map * Conversion.extra_goals
val set_current_sigma : depth:int -> State.t -> Evd.evar_map -> State.t * Conversion.extra_goals
val get_global_env_current_sigma : depth:int ->
  Data.hyps -> constraints -> State.t -> State.t * empty coq_context * Evd.evar_map * Conversion.extra_goals

(* HOAS of terms *)
val constr2lp :
  depth:int -> ?calldepth:int -> full coq_context -> constraints -> State.t ->
  EConstr.t -> State.t * term * Conversion.extra_goals

(* readback: adds to the evar map universes and evars in the term *)
val lp2constr :
  depth:int -> full coq_context -> constraints -> State.t -> 
  term -> State.t * EConstr.t * Conversion.extra_goals

(* variants in the global context *)
val constr2lp_closed : depth:int -> ?calldepth:int -> empty coq_context -> constraints -> State.t ->
  EConstr.t -> State.t * term * Conversion.extra_goals
val lp2constr_closed :  depth:int -> empty coq_context -> constraints -> State.t ->
  term -> State.t * EConstr.t * Conversion.extra_goals
val constr2lp_closed_ground : depth:int -> ?calldepth:int -> empty coq_context -> constraints -> State.t ->
  EConstr.t -> State.t * term * Conversion.extra_goals
val lp2constr_closed_ground :  depth:int -> empty coq_context -> constraints -> State.t ->
  term -> State.t * EConstr.t * Conversion.extra_goals

(* another variant, to call the pretyper *)
val lp2skeleton :
  depth:int -> full coq_context -> constraints -> State.t ->
  term -> State.t * Glob_term.glob_constr * Conversion.extra_goals

type coercion_status = Regular | Off | Reversible
type record_field_spec = { name : Name.t; is_coercion : coercion_status; is_canonical : bool }

[%%if coq = "8.20" || coq = "9.0"]
val lp2inductive_entry :
  depth:int -> empty coq_context -> constraints -> State.t -> term ->
  State.t * (DeclareInd.default_dep_elim list * Entries.mutual_inductive_entry * Univ.ContextSet.t * UnivNames.universe_binders * (bool * record_field_spec list) option * DeclareInd.one_inductive_impls list) * Conversion.extra_goals
[%%else]
val lp2inductive_entry :
  depth:int -> empty coq_context -> constraints -> State.t -> term ->
  State.t * (DeclareInd.default_dep_elim list * Entries.mutual_inductive_entry * Univ.ContextSet.t * UState.named_universes_entry * (bool * record_field_spec list) option * DeclareInd.one_inductive_impls list) * Conversion.extra_goals
[%%endif]

val inductive_decl2lp :
  depth:int -> empty coq_context -> constraints -> State.t -> (Names.MutInd.t * UVars.Instance.t * (Declarations.mutual_inductive_body * Declarations.one_inductive_body) * (Glob_term.binding_kind list * Glob_term.binding_kind list list)) ->
    State.t * term * Conversion.extra_goals

val inductive_entry2lp :
  depth:int -> empty coq_context -> constraints -> State.t -> loose_udecl:bool -> ComInductive.Mind_decl.t ->
    State.t * term * Conversion.extra_goals

val record_entry2lp :
  depth:int -> empty coq_context -> constraints -> State.t -> loose_udecl:bool ->Record.Record_decl.t ->
    State.t * term * Conversion.extra_goals
  
val in_elpi_id : Names.Name.t -> term
val in_elpi_bool : State.t -> bool -> term
val in_elpi_parameter : Names.Name.t -> imp:term -> term -> term -> term
val in_elpi_arity : term -> term
val in_elpi_indtdecl_record : Names.Name.t -> term -> Names.Name.t -> term -> term
val in_elpi_indtdecl_endrecord : unit -> term
val in_elpi_indtdecl_field : depth:int -> State.t -> record_field_spec -> term -> term -> State.t * term
val in_elpi_indtdecl_inductive : State.t -> Declarations.recursivity_kind -> Names.Name.t -> term -> term list -> term
val in_elpi_indtdecl_constructor : Names.Name.t -> term -> term

val sealed_goal2lp : depth:int -> State.t -> Evar.t -> State.t * term * Conversion.extra_goals
val lp2goal : depth:int -> Data.hyps -> constraints -> State.t -> term -> 
  State.t * full coq_context * Evar.t * term list * Conversion.extra_goals

(* *** Low level API to reuse parts of the embedding *********************** *)
val unspec2opt : 'a Elpi.Builtin.unspec -> 'a option
val opt2unspec : 'a option -> 'a Elpi.Builtin.unspec

val in_elpi_gr : depth:int -> State.t -> Names.GlobRef.t -> term
val in_elpi_poly_gr : depth:int -> State.t -> Names.GlobRef.t -> term -> term
val in_elpi_poly_gr_instance : depth:int -> State.t -> Names.GlobRef.t -> UVars.Instance.t -> term
val in_elpi_flex_sort : term -> term
val in_elpi_sort : depth:int -> 'a coq_context -> constraints -> state -> Sorts.t -> state * term * Conversion.extra_goals
val in_elpi_prod : Name.t -> term -> term -> term
val in_elpi_lam : Name.t -> term -> term -> term
val in_elpi_let : Name.t -> term -> term -> term -> term
val in_elpi_appl : depth:int -> term -> term list -> term
val in_elpi_match : term -> term -> term list -> term
val in_elpi_fix : Name.t -> int -> term -> term -> term
val in_elpi_name : Name.t -> term

val set_coq : Elpi.API.Ast.Scope.language -> unit

(* gref *)
val in_elpiast_gref : loc:Ast.Loc.t -> Names.GlobRef.t -> Ast.Term.t
(* term *)
val in_elpiast_gr : loc:Ast.Loc.t -> Names.GlobRef.t -> Ast.Term.t
val in_elpiast_poly_gr : loc:Ast.Loc.t -> Names.GlobRef.t -> Ast.Term.t -> Ast.Term.t
val in_elpiast_poly_gr_instance : loc:Ast.Loc.t -> Names.GlobRef.t -> UVars.Instance.t -> Ast.Term.t
val in_elpiast_flex_sort : loc:Ast.Loc.t -> Ast.Term.t -> Ast.Term.t
val in_elpiast_sort : loc:Ast.Loc.t -> state -> Sorts.t -> Ast.Term.t
val in_elpiast_prod : loc:Ast.Loc.t -> Names.Name.t -> Ast.Term.t -> Ast.Term.t -> Ast.Term.t
val in_elpiast_lam : loc:Ast.Loc.t -> Names.Name.t -> Ast.Term.t -> Ast.Term.t -> Ast.Term.t
val in_elpiast_let : loc:Ast.Loc.t -> Names.Name.t -> ty:Ast.Term.t -> bo:Ast.Term.t -> Ast.Term.t -> Ast.Term.t
val in_elpiast_appl : loc:Ast.Loc.t -> Ast.Term.t -> Ast.Term.t list -> Ast.Term.t
val in_elpiast_match : loc:Ast.Loc.t -> Ast.Term.t -> Ast.Term.t -> Ast.Term.t list -> Ast.Term.t
val in_elpiast_fix : loc:Ast.Loc.t -> Names.Name.t -> int -> Ast.Term.t -> Ast.Term.t -> Ast.Term.t
val in_elpiast_name : loc:Ast.Loc.t -> Names.Name.t -> Ast.Term.t
val in_elpiast_decl : loc:Ast.Loc.t -> v:Ast.Term.t -> Names.Name.t -> ty:Ast.Term.t -> Ast.Term.t
val in_elpiast_def : loc:Ast.Loc.t -> v:Ast.Term.t -> Names.Name.t -> ty:Ast.Term.t -> bo:Ast.Term.t -> Ast.Term.t

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
val sort : (Sorts.t,'a coq_context,constraints) ContextualConversion.t
val global_constant_of_globref : Names.GlobRef.t -> global_constant
val abbreviation : Globnames.abbreviation Conversion.t
val implicit_kind : Glob_term.binding_kind Conversion.t
val collect_term_variables : depth:int -> term -> Names.Id.t list
type pstring = Pstring.t
type primitive_value =
  | Uint63 of Uint63.t
  | Float64 of Float64.t
  | Pstring of pstring
  | Projection of Projection.t
val primitive_value : primitive_value Conversion.t
val in_elpi_primitive : depth:int -> state -> primitive_value -> state * term
val in_elpiast_primitive : loc:Ast.Loc.t -> primitive_value -> Ast.Term.t 

val uinstance : UVars.Instance.t Conversion.t

val universe_constraint : Univ.univ_constraint Conversion.t
val universe_variance : (Univ.Level.t * UVars.Variance.t option) Conversion.t
val universe_decl : universe_decl Conversion.t
val universe_decl_cumul : universe_decl_cumul Conversion.t

module GRMap : Elpi.API.Utils.Map.S with type key = Names.GlobRef.t
module GRSet : Elpi.API.Utils.Set.S with type elt = Names.GlobRef.t

module UnivMap : Elpi.API.Utils.Map.S with type key = Univ.Universe.t
module UnivSet : Elpi.API.Utils.Set.S with type elt = Univ.Universe.t

module UnivLevelMap : Elpi.API.Utils.Map.S with type key = Univ.Level.t
module UnivLevelSet : Elpi.API.Utils.Set.S with type elt = Univ.Level.t


val compute_with_uinstance :
  depth:int -> options -> state ->
  (state -> 'a -> UVars.Instance.t option -> state * 'c * UVars.Instance.t option) ->
  'a ->
  UVars.Instance.t option ->
    state * 'c * UVars.Instance.t option * Conversion.extra_goals

(* CData relevant for other modules, e.g the one exposing Coq's API *)
val universe_level_variable : Univ.Level.t Conversion.t
val univ : Univ.Universe.t Conversion.t
val isuniv : RawOpaqueData.t -> bool
val univout : RawOpaqueData.t -> Univ.Universe.t

val is_sort : depth:int -> term -> bool
val is_prod : depth:int -> term -> (term * term) option (* ty, bo @ depth+1 *)
val is_let : depth:int -> term -> (term * term * term) option (* ty, d, bo @ depth+1 *)
val is_lam : depth:int -> term -> (term * term) option (* ty, bo @ depth+1 *)

val isname : RawOpaqueData.t -> bool
val nameout : RawOpaqueData.t -> Name.t
val name : Name.t Conversion.t

type global_or_pglobal =
  | Global of term option
  | PGlobal of term option * UVars.Instance.t option
  | NotGlobal
  | Var
val is_global_or_pglobal : depth:int -> term -> global_or_pglobal

val in_elpi_modpath : ty:bool -> Names.ModPath.t -> term
val is_modpath : depth:int -> term -> bool
val is_modtypath : depth:int -> term -> bool
val in_coq_modpath : depth:int -> term -> Names.ModPath.t
val modpath : Names.ModPath.t Conversion.t
val modtypath : Names.ModPath.t Conversion.t
val module_inline_default : Declaremods.inline Conversion.t
val reduction_flags : RedFlags.reds Conversion.t

type module_item =
  | Module of Names.ModPath.t * module_item list
  | ModuleType of Names.ModPath.t
  | Gref of Names.GlobRef.t
  | Functor of Names.ModPath.t * Names.ModPath.t list
  | FunctorType of Names.ModPath.t * Names.ModPath.t list

[%%if coq = "8.20" || coq = "9.0"]
val in_elpi_module : depth:int -> State.t -> ModPath.t -> Declarations.module_body -> module_item list
val in_elpi_module_type : Declarations.module_type_body -> string list
[%%else]
val in_elpi_module : depth:int -> State.t -> ModPath.t -> Mod_declarations.module_body -> module_item list
val in_elpi_module_type : Mod_declarations.module_type_body -> string list
[%%endif]

val coercion_status : coercion_status Conversion.t
type record_field_att =
  | Coercion of coercion_status
  | Canonical of bool
val record_field_att : record_field_att Conversion.t

val add_constraints : State.t -> UnivProblem.Set.t -> State.t
val mk_global : State.t -> Names.GlobRef.t -> UVars.Instance.t option ->
  State.t * EConstr.t * UVars.Instance.t option
val poly_ctx_size_of_gref : Environ.env -> Names.GlobRef.t -> int * int
val body_of_constant :
  State.t -> Names.Constant.t -> UVars.Instance.t option ->
  State.t * EConstr.t option * UVars.Instance.t option

val grab_global_env : uctx:Univ.ContextSet.t -> State.t -> State.t
val grab_global_env_drop_univs_and_sigma : State.t -> State.t
val grab_global_env_drop_sigma : State.t -> State.t
val grab_global_env_drop_sigma_keep_univs : uctx:Univ.ContextSet.t -> State.t -> State.t

val mk_decl : depth:int -> Name.t -> ty:term -> term
(* Adds an Arg for the normal form with ctx_len context entry vars in scope *)

val mk_def :
  depth:int -> Name.t -> bo:term -> ty:term -> term

val get_global_env : State.t -> Environ.env
val get_sigma : State.t -> Evd.evar_map
val update_sigma : State.t -> (Evd.evar_map -> Evd.evar_map) -> State.t

type hyp = { ctx_entry : term; depth : int }

val solvegoals2query :
  Evd.evar_map -> Evar.t list -> Elpi.API.Ast.Loc.t -> main:'a list ->
  in_elpi_tac_arg:(base:'base -> depth:int -> ?calldepth:int -> 'b coq_context -> hyp list -> Evd.evar_map -> State.t -> 'a -> State.t * term list * Conversion.extra_goals) ->
  depth:int -> base:'base -> State.t -> State.t * term * Conversion.extra_goals
val txtgoals2query :
  Evd.evar_map -> Evar.t list -> Elpi.API.Ast.Loc.t -> main:string ->
  depth:int -> base:Elpi.API.Compile.program -> State.t -> State.t * term * Conversion.extra_goals

val tclSOLUTION2EVD : eta_contract_solution:bool -> Evd.evar_map -> Elpi.API.Data.solution -> unit Proofview.tactic
val solution2evd : eta_contract_solution:bool -> Evd.evar_map -> Elpi.API.Data.solution -> Evar.Set.t -> Evd.evar_map * Evar.t list * Evar.t list

val show_coq_engine : ?with_univs:bool -> State.t -> string
val show_coq_elpi_engine_mapping : State.t -> string

val type_of_global : state -> GlobRef.t -> UVars.Instance.t option -> state * (EConstr.t * UVars.Instance.t)
val minimize_universes : state -> state
val new_univ_level_variable : ?flexible:bool -> state -> state * (Univ.Level.t * Univ.Universe.t)
val constraint_eq : Sorts.t -> Sorts.t -> UnivProblem.t
val constraint_leq : Sorts.t -> Sorts.t -> UnivProblem.t
val add_universe_constraint : state -> UnivProblem.t -> state
val force_level_of_universe : state -> Univ.Universe.t -> state * Univ.Level.t * Univ.Universe.t * Sorts.t
val purge_algebraic_univs_sort : state -> EConstr.ESorts.t -> state * Sorts.t
val ideclc : constant
val uideclc : constant
val poly_cumul_udecl_variance_of_options : state -> options -> state * bool * bool * UState.universe_decl * Entries.variance_entry
val merge_universe_context : state -> UState.t -> state
val restricted_sigma_of : Univ.Level.Set.t -> state -> Evd.evar_map
val universes_of_term : state -> EConstr.t -> Univ.Level.Set.t
val universes_of_udecl : state -> UState.universe_decl -> Univ.Level.Set.t

