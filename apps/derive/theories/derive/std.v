(* Standard set of derivations

   license: GNU Lesser General Public License Version 2.1 or later
   ------------------------------------------------------------------------- *)

From elpi.apps Require Export derive.
From elpi.apps Require Import
  derive.map
  derive.lens_laws
  derive.eqbcorrect
  derive.param2
.
Elpi Typecheck derive.

(* we derive the Coq prelude *)

Module Prelude.
Module Empty_set. derive Init.Datatypes.Empty_set "". End Empty_set.
Module unit. derive Init.Datatypes.unit "". End unit.
Module bool. derive Init.Datatypes.bool "". End bool.
Module nat. derive Init.Datatypes.nat "". End nat.
Module option. derive Init.Datatypes.option "". End option.
Module sum. derive Init.Datatypes.sum "". End sum.
Module prod. derive Init.Datatypes.prod "". End prod.
Module list. derive Init.Datatypes.list "". End list.
Module comparison. derive Init.Datatypes.comparison "". End comparison.
End Prelude.

Export Prelude.
