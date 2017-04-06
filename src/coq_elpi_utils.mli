(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

val err : Pp.std_ppcmds -> 'a
val nYI : string -> 'a
val kind : depth:int -> Elpi_runtime.term -> Elpi_runtime.term
val safe_destApp : 
  Constr.t -> (Constr.t,Constr.types) Constr.kind_of_term * Constr.t array
val mkGHole : Glob_term.glob_constr
val debug : bool ref
