(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Names
open Elpi_runtime

val in_elpi_gr : Globnames.global_reference -> term
val in_elpi_sort : Sorts.t -> term
val in_elpi_prod : Name.t -> term -> term -> term
val in_elpi_lam : Name.t -> term -> term -> term
val in_elpi_let : Name.t -> term -> term -> term -> term
val in_elpi_implicit : term
val in_elpi_appl : term -> term list -> term
val in_elpi_match : term -> term -> term array -> term
val in_elpi_fix : Name.t -> int -> term -> term -> term

val isgr : Elpi_util.CData.t -> bool
val grout : Elpi_util.CData.t -> Globnames.global_reference


val constr2lp : Constr.t -> term
val lp2constr : term -> Constr.t
