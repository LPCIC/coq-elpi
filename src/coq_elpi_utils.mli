(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

val err : Pp.t -> 'a
val nYI : string -> 'a
val safe_destApp : 
  Constr.t -> (Constr.t,Constr.types,Sorts.t, Univ.Instance.t) Constr.kind_of_term * Constr.t array
val mkGHole : Glob_term.glob_constr
val pp2string : (Format.formatter -> 'a -> unit) -> 'a -> string
val mkApp : depth:int -> Elpi_API.Extend.Data.term -> Elpi_API.Extend.Data.term list -> Elpi_API.Extend.Data.term

val string_split_on_char : char -> string -> string list
