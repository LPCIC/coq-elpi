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
