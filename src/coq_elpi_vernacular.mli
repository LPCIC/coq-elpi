(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Coq_elpi_utils
open Coq_elpi_programs
open Coq_elpi_arg_HOAS

val atts2impl :
Elpi.API.Ast.Loc.t -> Summary.Stage.t -> depth:int -> Elpi.API.State.t -> Attributes.vernac_flags ->
  Elpi.API.Data.term -> Elpi.API.State.t * Elpi.API.Data.term

module type Common = sig
  val typecheck_program : ?program:qualified_name -> unit -> unit

  val get_and_compile :
    qualified_name -> (Elpi.API.Compile.program * bool) option
  val run : static_check:bool ->
    Elpi.API.Compile.program ->
     [ `Ast of (Elpi.API.State.t -> Elpi.API.State.t) * Elpi.API.Ast.query
     | `Fun of
         depth:int ->
         Elpi.API.State.t ->
         Elpi.API.State.t *
         (Elpi.API.Ast.Loc.t * Elpi.API.Data.term) *
         Elpi.API.Conversion.extra_goals ] ->
    unit Elpi.API.Execute.outcome

  val accumulate_files       : atts:((Str.regexp list option * Str.regexp list option) * phase option) -> ?program:qualified_name -> string list -> unit
  val accumulate_extra_deps  : atts:((Str.regexp list option * Str.regexp list option) * phase option) -> ?program:qualified_name -> Names.Id.t list -> unit
  val accumulate_string      : atts:((Str.regexp list option * Str.regexp list option) * phase option) -> ?program:qualified_name -> Elpi.API.Ast.Loc.t * string -> unit
  val accumulate_db          : atts:((Str.regexp list option * Str.regexp list option) * phase option) -> ?program:qualified_name -> qualified_name -> unit
  val accumulate_to_db       : atts:((Str.regexp list option * Str.regexp list option) * phase option) -> qualified_name -> Elpi.API.Ast.Loc.t * string -> Names.Id.t list -> scope:Coq_elpi_utils.clause_scope -> unit

  (* Setup *)
  val load_checker : string -> unit
  val load_printer : string -> unit
  val load_tactic : string -> unit
  val load_command : string -> unit
  
  val debug         : atts:phase option -> string list -> unit
  val trace         : atts:phase option -> int -> int -> string list -> string list -> unit
  val trace_browser : atts:phase option -> string list -> unit
  val bound_steps   : atts:phase option -> int -> unit
  val print         : atts:phase option -> name:qualified_name -> args:string list -> string -> unit

  val create_program : atts:bool option -> program_name -> init:(Elpi.API.Ast.Loc.t * string) -> unit
  val create_command : atts:bool option -> program_name -> unit
  val create_tactic : program_name -> unit
  val create_db : atts:phase option -> program_name -> init:(Elpi.API.Ast.Loc.t * string) -> unit

end

module Synterp : sig include Common
val run_program : Loc.t -> qualified_name -> atts:Attributes.vernac_flags -> Cmd.raw list -> (Vernacstate.Synterp.t * (target:Elpi.API.State.t -> depth:int -> (Elpi.API.Data.term,string) Stdlib.Result.t) * Coq_elpi_builtins_synterp.SynterpAction.RZipper.zipper) option
val run_in_program : ?program:qualified_name -> Elpi.API.Ast.Loc.t * string -> Coq_elpi_builtins_synterp.SynterpAction.RZipper.zipper option

end
module Interp : sig include Common
val run_program : Loc.t -> qualified_name -> atts:Attributes.vernac_flags -> syndata:(Vernacstate.Synterp.t * (target:Elpi.API.State.t -> depth:int -> (Elpi.API.Data.term,string) Stdlib.Result.t) * Coq_elpi_builtins_synterp.SynterpAction.RZipper.zipper) option -> Cmd.raw list -> unit
val run_in_program : ?program:qualified_name -> syndata:Coq_elpi_builtins_synterp.SynterpAction.RZipper.zipper option -> Elpi.API.Ast.Loc.t * string -> unit
end

val document_builtins : unit -> unit



val run_tactic : Loc.t -> qualified_name -> atts:Attributes.vernac_flags -> Geninterp.interp_sign -> Tac.top list -> unit Proofview.tactic
val run_in_tactic : ?program:qualified_name -> Elpi.API.Ast.Loc.t * string -> Geninterp.interp_sign -> unit Proofview.tactic

(* move to synterp *)
val export_command : ?as_:qualified_name -> qualified_name -> unit
