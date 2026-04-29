(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi.API
open Rocq_elpi_utils

type cunit = Full of  Names.KerName.t * Compile.compilation_unit | Signature of Compile.compilation_unit_signature
val name_of_cunit : cunit -> string
type program_name = Loc.t * qualified_name
type what = Code | SignatureOnly

type src =
  | File of src_file
  | DatabaseBody of qualified_name
  | DatabaseHeader of src_db_header
and src_file = {
  fname : string;
  fast : cunit;
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
  val unit_from_ast    : ?error_header:string -> elpi:Setup.elpi -> base:Compile.program -> loc:Loc.t -> Compile.scoped_program -> cunit
  val parse_goal       : elpi:Setup.elpi -> loc:Loc.t -> Ast.Loc.t -> string -> Ast.query

  val db_exists : qualified_name -> bool
  val program_exists : qualified_name -> bool
  val declare_db : program_name -> unit
  val declare_program : program_name -> nature -> unit
  val declare_file : program_name -> unit
  val get_nature : qualified_name -> nature

  val init_program : program_name -> loc:Loc.t -> (Ast.Loc.t * string) -> unit
  val init_command : program_name -> loc:Loc.t -> unit
  val init_tactic  : program_name -> loc:Loc.t -> unit
  val init_db      : program_name -> loc:Loc.t -> (Ast.Loc.t * string) -> unit
  val init_file    : program_name -> loc:Loc.t -> (Ast.Loc.t * string) -> unit

  val ast_of_elpifile : qualified_name -> Compile.scoped_program list

  type db_header
  val header_of_db : qualified_name -> db_header

  val accumulate_file_to_program     : loc:Loc.t -> program:qualified_name -> what:what -> file:string -> unit
  val accumulate_ast_to_program      : loc:Loc.t -> program:qualified_name -> what:what -> ast:Compile.scoped_program -> unit
  val accumulate_string_to_program   : loc:Loc.t -> program:qualified_name -> code:(Ast.Loc.t * string) -> unit
  val accumulate_plugin_to_program   : loc:Loc.t -> program:qualified_name -> plugin:Elpi.API.Setup.builtins -> unit
  val accumulate_db_to_program       : loc:Loc.t -> program:qualified_name -> db:qualified_name -> unit
  val accumulate_header_to_program   : loc:Loc.t -> program:qualified_name -> header:db_header -> unit

  val accumulate_file_to_db   : loc:Loc.t -> db:qualified_name -> what:what -> file:string -> scope:Rocq_elpi_utils.clause_scope -> unit
  val accumulate_ast_to_db    : loc:Loc.t -> db:qualified_name -> what:what -> ast:Compile.scoped_program -> scope:Rocq_elpi_utils.clause_scope -> unit
  val accumulate_string_to_db : loc:Loc.t -> db:qualified_name -> code:(Ast.Loc.t * string) -> scope:Rocq_elpi_utils.clause_scope -> unit
  val accumulate_units_to_db  : loc:Loc.t -> db:qualified_name -> units:cunit list -> secvars:Names.Id.t list -> scope:Rocq_elpi_utils.clause_scope -> unit
  val accumulate_header_to_db : loc:Loc.t -> db:qualified_name -> header:db_header -> scope:Rocq_elpi_utils.clause_scope -> unit

  val load_command : loc:Loc.t -> string -> unit
  val load_tactic : loc:Loc.t -> string -> unit

  val ensure_initialized : unit -> Setup.elpi

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
