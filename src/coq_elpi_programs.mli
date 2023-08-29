(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi.API
open Coq_elpi_utils

type cunit = Names.KerName.t * Compile.compilation_unit
type program_name = Loc.t * qualified_name

type src =
  | File of src_file
  | EmbeddedString of src_string
  | Database of qualified_name
and src_file = {
  fname : string;
  fast : cunit;
}
and src_string = {
  sloc : Ast.Loc.t;
  sdata : string;
  sast : cunit;
}
type nature = Command of { raw_args : bool } | Tactic | Program of { raw_args : bool } 

val get_nature : qualified_name -> nature
val create_program : program_name -> nature -> src -> unit
val create_db : program_name -> cunit -> unit
val set_current_program : qualified_name -> unit
val current_program : unit -> qualified_name
val accumulate : qualified_name -> src list -> unit
val accumulate_to_db : qualified_name -> cunit list -> Names.Id.t list -> scope:Coq_elpi_utils.clause_scope -> unit
val group_clauses : 
  (qualified_name * Ast.program * Names.variable list * clause_scope) list ->
  (qualified_name * Ast.program list * Names.variable list * clause_scope) list
val load_checker : string -> unit
val load_printer : string -> unit
val load_command : string -> unit
val load_tactic : string -> unit
val document_builtins : unit -> unit
val ensure_initialized : unit -> Setup.elpi
val db_exists : qualified_name -> bool
val checker : unit -> Compile.compilation_unit list
val printer : unit -> Compile.compilation_unit
val tactic_init : unit -> src
val command_init : unit -> src
val combine_hash : int -> int -> int

module Chunk : sig
  type t =
  | Base of {
      hash : int;
      base : cunit;
    }
  | Snoc of {
      source_rev : cunit list;
      prev : t;
      hash : int
    }
  val hash : t -> int
  val eq : t -> t -> bool
end
  
module Code : sig
  type 'db t =
  | Base of {
      hash : int;
      base : cunit;
      }
  | Snoc of {
      source : cunit;
      prev : 'db t;
      hash : int;
      cacheme: bool;
      }
  | Snoc_db of {
      chunks : 'db;
      prev : 'db t;
      hash : int
      }
  val hash : 'db t -> int
  val cache : 'db t -> bool
  val eq : ('db -> 'db -> bool) -> 'db t -> 'db t -> bool
end

val code : qualified_name -> Chunk.t Code.t
val debug_vars : Compile.StrSet.t ref
val cc_flags : unit -> Compile.flags
val unit_from_file   : elpi:Setup.elpi -> string -> cunit
val unit_from_string : elpi:Setup.elpi -> Ast.Loc.t -> string -> cunit
val assemble_units : elpi:Setup.elpi -> Compile.compilation_unit list -> Compile.program
val extend_w_units : base:Compile.program -> Compile.compilation_unit list -> Compile.program
val parse_goal : elpi:Setup.elpi -> Ast.Loc.t -> string -> Ast.query
val intern_unit : (string option * Compile.compilation_unit * Compile.flags) -> cunit

module SLMap : Map.S with type key = qualified_name
