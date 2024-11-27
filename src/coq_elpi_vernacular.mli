(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Coq_elpi_utils
open Coq_elpi_programs
open Coq_elpi_arg_HOAS

val atts2impl :
  depth:int -> Elpi.API.Ast.Loc.t -> Summary.Stage.t -> Elpi.API.State.t -> Attributes.vernac_flags ->
  Elpi.API.Data.term -> Elpi.API.State.t * Elpi.API.Data.term

type query =
  | Ast of (Elpi.API.Data.state -> Elpi.API.Data.state) * Elpi.API.Ast.query
  | Fun of (Elpi.API.Data.state -> Elpi.API.Data.state * Elpi.API.RawData.term * Elpi.API.Conversion.extra_goals)

type atts = ((clause_scope * (Str.regexp list option * Str.regexp list option)) * phase option)
type what = Code | Signature

module type Common = sig

  val get_and_compile :
    loc:Loc.t -> qualified_name -> (Elpi.API.Compile.program * bool) option
  val run : loc:Loc.t ->
    Elpi.API.Compile.program -> query ->
    Elpi.API.Execute.outcome

  val accumulate_files       : atts:atts -> loc:Loc.t -> ?program:qualified_name -> string list -> unit
  val accumulate_extra_deps  : atts:atts -> loc:Loc.t -> ?program:qualified_name -> what:what -> qualified_name list -> unit
  val accumulate_string      : atts:atts -> loc:Loc.t -> ?program:qualified_name -> Elpi.API.Ast.Loc.t * string -> unit
  val accumulate_db          : atts:atts -> loc:Loc.t -> ?program:qualified_name -> qualified_name -> unit
  val accumulate_db_header   : atts:atts -> loc:Loc.t -> ?program:qualified_name -> qualified_name -> unit
  val accumulate_to_db       : atts:atts -> loc:Loc.t -> qualified_name -> Elpi.API.Ast.Loc.t * string -> Names.Id.t list -> unit

  (* Setup *)
  val load_tactic  : loc:Loc.t -> string -> unit
  val load_command : loc:Loc.t -> string -> unit
  
  val debug         : atts:phase option -> string list -> unit
  val trace         : atts:phase option -> int -> int -> string list -> string list -> unit
  val trace_browser : atts:phase option -> string list -> unit
  val bound_steps   : atts:phase option -> int -> unit
  val print         : atts:phase option -> loc:Loc.t -> name:qualified_name -> args:string list -> string -> unit

  val create_program : atts:bool option -> loc:Loc.t -> program_name -> init:(Elpi.API.Ast.Loc.t * string) -> unit
  val create_command : atts:bool option -> loc:Loc.t -> program_name -> unit
  val create_tactic : loc:Loc.t -> program_name -> unit
  val create_db : atts:phase option -> loc:Loc.t -> program_name -> init:(Elpi.API.Ast.Loc.t * string) -> unit
  val create_file : atts:phase option -> loc:Loc.t -> program_name -> init:(Elpi.API.Ast.Loc.t * string) -> unit

end

module Synterp : sig include Common
val run_program : loc:Loc.t -> qualified_name -> atts:Attributes.vernac_flags -> Cmd.raw list -> (Vernacstate.Synterp.t * (target:Elpi.API.Compile.program -> depth:int -> (Elpi.API.Data.term,string) Stdlib.Result.t) * Coq_elpi_builtins_synterp.SynterpAction.RZipper.zipper) option
val run_in_program : loc:Loc.t -> ?program:qualified_name -> Elpi.API.Ast.Loc.t * string -> Coq_elpi_builtins_synterp.SynterpAction.RZipper.zipper option

end
module Interp : sig include Common
val run_program : loc:Loc.t -> qualified_name -> atts:Attributes.vernac_flags -> syndata:(Vernacstate.Synterp.t * (target:Elpi.API.Compile.program -> depth:int -> (Elpi.API.Data.term,string) Stdlib.Result.t) * Coq_elpi_builtins_synterp.SynterpAction.RZipper.zipper) option -> Cmd.raw list -> unit
val run_in_program : loc:Loc.t -> ?program:qualified_name -> syndata:Coq_elpi_builtins_synterp.SynterpAction.RZipper.zipper option -> Elpi.API.Ast.Loc.t * string -> unit
end

val document_builtins : unit -> unit



val run_tactic : loc:Loc.t -> qualified_name -> atts:Attributes.vernac_flags -> Geninterp.interp_sign -> Tac.top list -> unit Proofview.tactic
val run_in_tactic : loc:Loc.t -> ?program:qualified_name -> Elpi.API.Ast.Loc.t * string -> Geninterp.interp_sign -> unit Proofview.tactic

(* move to synterp *)
val export_command : ?as_:qualified_name -> qualified_name -> unit
