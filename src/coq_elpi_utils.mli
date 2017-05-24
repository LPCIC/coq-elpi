(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

val err : Pp.std_ppcmds -> 'a
val nYI : string -> 'a
val kind : depth:int -> Elpi_API.Data.term -> Elpi_API.Data.term
val safe_destApp : 
  Constr.t -> (Constr.t,Constr.types,Sorts.t, Univ.Instance.t) Constr.kind_of_term * Constr.t array
val mkGHole : Glob_term.glob_constr
val pp2string : (Format.formatter -> 'a -> unit) -> 'a -> string
