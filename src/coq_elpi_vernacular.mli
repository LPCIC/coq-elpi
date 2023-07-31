(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Coq_elpi_utils
open Coq_elpi_programs

val create_program : ?raw_args:bool -> program_name -> init:(Elpi.API.Ast.Loc.t * string) -> unit
val create_command : ?raw_args:bool -> program_name -> unit
val create_tactic : program_name -> unit
val create_db : program_name -> init:(Elpi.API.Ast.Loc.t * string) -> unit

val typecheck_program : ?program:qualified_name -> unit -> unit

val accumulate_files  : ?program:qualified_name -> string list -> unit
val accumulate_extra_deps  : ?program:qualified_name -> Names.Id.t list -> unit
val accumulate_string : ?program:qualified_name -> Elpi.API.Ast.Loc.t * string -> unit
val accumulate_db     : ?program:qualified_name -> qualified_name -> unit

val accumulate_to_db  : qualified_name -> Elpi.API.Ast.Loc.t * string -> Names.Id.t list -> scope:Coq_elpi_utils.clause_scope -> unit

val skip : atts:(Str.regexp list option * Str.regexp list option) -> ('a -> unit) -> 'a -> unit

(* Setup *)
val load_checker : string -> unit
val load_printer : string -> unit
val load_tactic : string -> unit
val load_command : string -> unit
val document_builtins : unit -> unit

val solve_TC : qualified_name -> 'a ->
    Evd.evar_map ->
    int option -> (* depth *)
    bool -> (* unique *)
    best_effort:bool ->
    (Evd.evar_map -> Evar.Set.elt -> bool) ->
    (bool * Evd.evar_map) option

(* Debug *)
val debug : string list -> unit
val trace : int -> int -> string list -> string list -> unit
val trace_browser : string list -> unit
val bound_steps : int -> unit
val print : qualified_name -> string list -> unit

open Coq_elpi_arg_HOAS

val run_program : Loc.t -> qualified_name -> atts:Attributes.vernac_flags -> Cmd.raw list -> unit
val run_in_program : ?program:qualified_name -> Elpi.API.Ast.Loc.t * string -> unit
val run_tactic : Loc.t -> qualified_name -> atts:Attributes.vernac_flags -> Geninterp.interp_sign -> Tac.top list -> unit Proofview.tactic
val run_in_tactic : ?program:qualified_name -> Elpi.API.Ast.Loc.t * string -> Geninterp.interp_sign -> unit Proofview.tactic

val export_command : qualified_name -> unit

val atts2impl :
  Elpi.API.Ast.Loc.t -> depth:int -> Elpi.API.State.t -> Attributes.vernac_flags ->
    Elpi.API.Data.term -> Elpi.API.State.t * Elpi.API.Data.term
val get_and_compile :
  qualified_name -> Elpi.API.Compile.program * bool
val run : static_check:bool ->
    Elpi.API.Compile.program ->
     [ `Ast of Elpi.API.Ast.query
     | `Fun of
         depth:int ->
         Elpi.API.State.t ->
         Elpi.API.State.t *
         (Elpi.API.Ast.Loc.t * Elpi.API.Data.term) *
         Elpi.API.Conversion.extra_goals ] ->
    unit Elpi.API.Execute.outcome