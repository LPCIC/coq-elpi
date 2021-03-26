(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)


val to_coq_loc : Elpi.API.Ast.Loc.t -> Loc.t
val of_coq_loc : Loc.t -> Elpi.API.Ast.Loc.t

val err : ?loc:Elpi.API.Ast.Loc.t -> Pp.t -> 'a
val nYI : string -> 'a
val safe_destApp : Evd.evar_map ->
  EConstr.t -> (EConstr.t,EConstr.types,EConstr.ESorts.t, EConstr.EInstance.t) Constr.kind_of_term * EConstr.t array
val mkGHole : Glob_term.glob_constr
val pp2string : (Format.formatter -> 'a -> unit) -> 'a -> string
val mkApp : depth:int -> Elpi.API.RawData.term -> Elpi.API.RawData.term list -> Elpi.API.RawData.term

val string_split_on_char : char -> string -> string list
val mk_gforall : Glob_term.glob_constr -> Glob_term.glob_decl list -> Glob_term.glob_constr
val mk_gfun : Glob_term.glob_constr -> Glob_term.glob_decl list -> Glob_term.glob_constr
val manual_implicit_of_biding_kind : Names.Name.t -> Glob_term.binding_kind -> (Names.Name.t * bool) option CAst.t
val manual_implicit_of_gdecl : Glob_term.glob_decl -> (Names.Name.t * bool) option CAst.t
val implicit_kind_of_binding_kind : Glob_term.binding_kind -> Impargs.implicit_kind
val manual_implicit_of_implicit_kind : Names.Name.t -> Impargs.implicit_kind -> (Names.Name.t * bool) option CAst.t
val lookup_inductive : Environ.env -> Names.inductive -> Declarations.mutual_inductive_body * Declarations.one_inductive_body
val fold_elpi_term :
  (depth:int -> 'a -> Elpi.API.Data.term -> 'a) ->
    'a -> depth:int -> Elpi.API.RawData.view -> 'a