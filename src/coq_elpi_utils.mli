(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)


val to_coq_loc : Elpi.API.Ast.Loc.t -> Loc.t
val of_coq_loc : Loc.t -> Elpi.API.Ast.Loc.t

val elpi_cat : CWarnings.category
val elpi_depr_cat : CWarnings.category

val err : ?loc:Elpi.API.Ast.Loc.t -> Pp.t -> 'a
exception LtacFail of int * Pp.t
val ltac_fail_err : ?loc:Elpi.API.Ast.Loc.t -> int -> Pp.t -> 'a
val nYI : string -> 'a
val safe_destApp : Evd.evar_map ->
  EConstr.t -> (EConstr.t,EConstr.types,EConstr.ESorts.t, EConstr.EInstance.t) Constr.kind_of_term * EConstr.t array
val mkGHole : Glob_term.glob_constr
val pp2string : (Format.formatter -> 'a -> unit) -> 'a -> string
val mkApp : depth:int -> Elpi.API.RawData.term -> Elpi.API.RawData.term list -> Elpi.API.RawData.term

val string_split_on_char : char -> string -> string list
val mk_gforall : Glob_term.glob_constr -> Glob_term.glob_decl list -> Glob_term.glob_constr
val mk_gfun : Glob_term.glob_constr -> Glob_term.glob_decl list -> Glob_term.glob_constr
val manual_implicit_of_binding_kind : Names.Name.t -> Glob_term.binding_kind -> (Names.Name.t * bool) option CAst.t
val manual_implicit_of_gdecl : Glob_term.glob_decl -> (Names.Name.t * bool) option CAst.t
val binding_kind_of_manual_implicit : (Names.Name.t * bool) option CAst.t -> Glob_term.binding_kind

val lookup_inductive : Environ.env -> Names.inductive -> Declarations.mutual_inductive_body * Declarations.one_inductive_body
val locate_gref : string -> Names.GlobRef.t
val locate_qualid : Libnames.qualid -> [ `Gref of Names.GlobRef.t | `Abbrev of Globnames.abbreviation ] option

val fold_elpi_term :
  (depth:int -> 'a -> Elpi.API.Data.term -> 'a) ->
    'a -> depth:int -> Elpi.API.RawData.view -> 'a

val uint63 : Uint63.t Elpi.API.Conversion.t
val float64 : Float64.t Elpi.API.Conversion.t
val projection : Names.Projection.t Elpi.API.Conversion.t

val debug : CDebug.t

type clause_scope = Local | Regular | Global | SuperGlobal
val pp_scope : Format.formatter -> clause_scope -> unit

val list_map_acc : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list

val detype : ?keepunivs:bool -> Environ.env -> Evd.evar_map -> EConstr.t -> Glob_term.glob_constr
val detype_closed_glob : Environ.env -> Evd.evar_map -> Ltac_pretype.closed_glob_constr -> Glob_term.glob_constr

type qualified_name = string list
val compare_qualified_name : qualified_name -> qualified_name -> int
val pr_qualified_name : qualified_name -> Pp.t
val show_qualified_name : qualified_name -> string
val pp_qualified_name : Format.formatter -> qualified_name -> unit

val option_map_acc : ('a -> 'b -> 'a * 'c) -> 'a -> 'b option -> 'a * 'c option
val option_map_acc2 : (Elpi.API.State.t -> 'b -> Elpi.API.State.t * 'c * Elpi.API.Conversion.extra_goals) -> Elpi.API.State.t -> 'b option -> Elpi.API.State.t * 'c option * Elpi.API.Conversion.extra_goals
val option_default : (unit -> 'a) -> 'a option -> 'a

val coq_version_parser : string -> int * int * int
