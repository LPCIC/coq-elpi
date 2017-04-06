(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

val is_coq_string : (Genarg.glob_generic_argument -> bool) ref
val get_coq_string : (Genarg.glob_generic_argument -> string) ref
