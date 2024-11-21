(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi.API
open Coq_elpi_utils

type cunit = Full of  Names.KerName.t * Compile.compilation_unit | Signature of Compile.compilation_unit_signature
type program_name = Loc.t * qualified_name

type src =
  | File of src_file
  | EmbeddedString of src_string
  | DatabaseBody of qualified_name
  | DatabaseHeader of src_db_header
and src_file = {
  fname : string;
  fast : cunit;
}
and src_string = {
  sast : cunit;
}
and src_db_header = {
  dast : cunit;
}

type nature = Command of { raw_args : bool } | Tactic | Program of { raw_args : bool }


module Chunk : sig
  type t =
  | Base of {
      hash : int;
      base : cunit list;
    }
  | Snoc of {
      source_rev : cunit list;
      prev : t;
      hash : int
    }
  val hash : t -> int
  val eq : t -> t -> bool
  val pp : Format.formatter -> t -> unit

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
  val pp : (Format.formatter -> 'db -> unit) -> Format.formatter -> 'db t -> unit
  val snoc_opt : cunit -> 'db t option -> 'db t
end

module SLMap : Map.S with type key = qualified_name

val combine_hash : int -> int -> int


(* runtime *)

module type Programs = sig

  val debug_vars : Compile.StrSet.t ref
  val cc_flags : unit -> Compile.flags
  val unit_from_file   : elpi:Setup.elpi -> base:Compile.program -> loc:Loc.t -> string -> cunit
  val unit_from_string : elpi:Setup.elpi -> base:Compile.program -> loc:Loc.t -> Ast.Loc.t -> string -> cunit
  val ast_from_string  : elpi:Setup.elpi -> loc:Loc.t -> Ast.Loc.t -> string -> Digest.t * Compile.scoped_program
  val unit_from_ast    : elpi:Setup.elpi -> base:Compile.program -> loc:Loc.t -> string option -> Compile.scoped_program -> cunit
  val extend_w_units   : base:Compile.program -> loc:Loc.t -> cunit list -> Compile.program
  val parse_goal       : elpi:Setup.elpi -> loc:Loc.t -> Ast.Loc.t -> string -> Ast.query

  val db_exists : qualified_name -> bool
  val program_exists : qualified_name -> bool
  val declare_db : program_name -> unit
  val declare_program : program_name -> nature -> unit
  val declare_file : program_name -> unit
  val get_nature : qualified_name -> nature

  val init_program : program_name -> src list -> unit
  val init_db : program_name -> loc:Loc.t -> (Ast.Loc.t * string) -> unit
  val init_file : program_name -> Digest.t * Compile.scoped_program -> unit

  val header_of_db : qualified_name -> cunit list
  val ast_of_file : qualified_name -> Digest.t * Compile.scoped_program

  val accumulate : qualified_name -> src list -> unit
  val accumulate_to_db : qualified_name -> cunit list -> Names.Id.t list -> scope:Coq_elpi_utils.clause_scope -> unit

  val load_command : loc:Loc.t -> string -> unit
  val load_tactic : loc:Loc.t -> string -> unit

  val ensure_initialized : unit -> Setup.elpi

  val tactic_init : unit -> src
  val command_init : unit -> src

  val code : ?even_if_empty:bool -> qualified_name -> Chunk.t Code.t option

  val in_stage : string -> string
  val stage : Summary.Stage.t
  val db_inspect : qualified_name -> int

  val get_and_compile_existing_db : loc:Loc.t -> qualified_name -> Compile.program
  val get_and_compile : loc:Loc.t -> ?even_if_empty:bool -> qualified_name -> (Compile.program * bool) option


end

(** [resolve_file_path ~must_exist ~allow_absolute ~only_elpi file] interprets
    file path [file] according to the Coq directory path configuration, taking
    into account the -Q and -R Coq options. If [file] is an absolute path, the
    functions returns [file] unchanged if [allow_absolute] is set, and gives a
    user error otherwise. Otherwise, [file] is expected to be of the following
    form: <coq_dir_path>/<rel_path>. The <coq_dir_path> part is expected to be
    a logical Coq directory, as mapped with -Q or -R. The <rel_path> part is a
    relative path from the corresponding directory. When [must_exist] is true,
    a user error is given when the resolved file does not exist (even if it is
    handled as an absolute path). When [only_elpi] is true, the function gives
    a path to a file with the ".elpi" extension, even in the case where [file]
    does not have an extension. *)
val resolve_file_path :
  must_exist:bool -> allow_absolute:bool -> only_elpi:bool -> string -> string

module Synterp : Programs
module Interp : Programs

val group_clauses : 
  (qualified_name * Ast.program * Names.variable list * clause_scope) list ->
  (qualified_name * Ast.program list * Names.variable list * clause_scope) list
val document_builtins : unit -> unit
