(* rocq-elpi: Coq terms as the object language of elpi                       *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module SynterpAction : sig
  type t
  val pp : t -> Pp.t

  (** Structured representation of a synterp action log. *)
  module Tree : sig
    type group

    val group_name : group -> string

    type node =
      | Group of group * tree
      | Action of t

    and tree = node list

    val to_list : tree -> t list

    val debug_pp : tree -> Pp.t
  end

  module WZipper : sig
    type zipper

    val collect : zipper -> Tree.tree
  end

  module RZipper : sig
    type zipper

    val collect : zipper -> Tree.tree

    val empty : zipper

    val is_empty : zipper -> [`Empty | `Group of Tree.group | `Action of t]

    val of_w : WZipper.zipper -> zipper
  end

  val log : WZipper.zipper Elpi.API.State.component
  val read : RZipper.zipper Elpi.API.State.component

  exception Error of Pp.t

  open Elpi.API
  open Elpi.Builtin
  open Names
  open Declaremods

  val synterp_state_after : t -> Vernacstate.Synterp.t

  type 'a replay = 'a -> State.t -> State.t * ModPath.t option

  val pop_BeginModule : (string * ModPath.t option unspec * (string * ModPath.t) list unspec) replay
  val pop_EndModule : unit replay
  val pop_BeginModuleType : (string * (string * ModPath.t) list unspec) replay
  val pop_EndModuleType : unit replay

  val pop_ApplyModule :
    (string * ModPath.t option unspec * ModPath.t unspec * ModPath.t list unspec * inline unspec) replay

  val pop_ApplyModuleType : (string * ModPath.t unspec * ModPath.t list unspec * inline unspec) replay
  val pop_IncludeModule : (ModPath.t * inline unspec) replay
  val pop_IncludeModuleType : (ModPath.t * inline unspec) replay
  val pop_ImportModule : ModPath.t replay
  val pop_ExportModule : ModPath.t replay
  val pop_BeginSection : string replay
  val pop_EndSection : unit replay

  val builtins_interp : Elpi.API.BuiltIn.declaration list
end

open Elpi.API
open Rocq_elpi_utils
open Names

val clauses_for_later_synterp :
  (qualified_name * Ast.program * Id.t list * Rocq_elpi_utils.clause_scope) list State.component

val set_accumulate_to_db_synterp :
  (loc:Loc.t -> (qualified_name * Ast.program * Id.t list * Rocq_elpi_utils.clause_scope) list -> unit) -> unit

val prop : Data.term Conversion.t
val id : string Conversion.t

type clause = string option * ([ `After | `Before | `Remove | `Replace ] * string) option * Data.term

val clause : clause Conversion.t

type scope = ExecutionSite | CurrentModule | Library

val scope : scope Conversion.t
val grafting : ([ `After | `Before | `Remove | `Replace ] * string) Conversion.t
val options : (Rocq_elpi_HOAS.options, Data.constraints) ContextualConversion.ctx_readback
val locate_module : BuiltIn.declaration
val locate_module_type : BuiltIn.declaration
val current_path : BuiltIn.declaration
val current_section_path : BuiltIn.declaration
val modpath_to_path : BuiltIn.declaration
val modtypath_to_path : BuiltIn.declaration
val modpath_to_library : BuiltIn.declaration
val modtypath_to_library : BuiltIn.declaration
val synterp_api_doc : string
val coq_synterp_builtins : BuiltIn.declaration list

type located =
  | LocGref of GlobRef.t
  | LocModule of ModPath.t
  | LocModuleType of ModPath.t
  | LocAbbreviation of Globnames.abbreviation

val located : located Conversion.t

type attribute_data =
  | AttributeString of string
  | AttributeLoc of Ast.Loc.t
type attribute_value =
  | AttributeEmpty
  | AttributeList of (string * attribute_value) list
  | AttributeLeaf of attribute_data

val attribute_value : attribute_value Conversion.t
val attribute : (string * attribute_value) Conversion.t

type accumulation_item = qualified_name * Ast.program * Id.t list * Rocq_elpi_utils.clause_scope

val accumulate_clauses :
  clauses_for_later:accumulation_item list State.component ->
  accumulate_to_db:(loc:Loc.t -> accumulation_item list -> unit) ->
  preprocess_clause:(depth:int -> Data.term -> Id.t list * Data.term) ->
  scope:scope Elpi.Builtin.unspec ->
  dbname:string ->
  clause list ->
  depth:int ->
  options:Rocq_elpi_HOAS.options ->
  State.t ->
  State.t * unit * Conversion.extra_goals

  (* To dump glob, we need a quick access to the invocation site loc *)
val invocation_site_loc : Ast.Loc.t State.component
val invocation_site_loc_synterp : Ast.Loc.t State.component
