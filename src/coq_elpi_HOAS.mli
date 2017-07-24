(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Names
open Elpi_API.Extend.Data
open Elpi_API.Extend

(* HOAS embedding and readback *)
val constr2lp : depth:int -> Constr.t -> term

val lp2constr : UState.t -> term -> UState.t * Constr.t

(* Low level API to reuse parts of the embedding *)
val in_elpi_gr : Globnames.global_reference -> term
val in_elpi_sort : Sorts.t -> term
val in_elpi_flex_sort : term -> term
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

val isuniv : CData.t -> bool
val univout : CData.t -> Univ.Universe.t
val univin : Univ.Universe.t -> CData.t

val nameout : CData.t -> Name.t

val new_univ : UState.t -> UState.t * Univ.Universe.t
