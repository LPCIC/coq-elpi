(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Names
open Elpi_API.Data
open Elpi_util

(* HOAS embedding and readback *)
val constr2lp : Constr.t -> term
val lp2constr : term -> Constr.t

(* Low level API to reuse parts of the embedding *)
val in_elpi_gr : Globnames.global_reference -> term
val in_elpi_sort : Sorts.t -> term
val in_elpi_prod : Name.t -> term -> term -> term
val in_elpi_lam : Name.t -> term -> term -> term
val in_elpi_let : Name.t -> term -> term -> term -> term
val in_elpi_appl : term -> term list -> term
val in_elpi_match : term -> term -> term list -> term
val in_elpi_fix : Name.t -> int -> term -> term -> term

val in_elpi_implicit : term
val in_elpi_axiom : term

val in_elpi_tt : term
val in_elpi_ff : term

val in_elpi_name : Name.t -> term

(* for quotations *)
val in_elpi_app_Arg : term -> term list -> term

(* CData relevant for other modules, e.g the one exposing Coq's API *)
val isgr : CData.t -> bool
val grout : CData.t -> Globnames.global_reference

