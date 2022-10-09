(* Standard set of derivations

   license: GNU Lesser General Public License Version 2.1 or later
   ------------------------------------------------------------------------- *)

From elpi.apps Require Export derive.
From elpi.apps Require Import
  derive.map
  derive.lens_laws
  derive.eqbOK
  derive.param2
.
Elpi Typecheck derive.

(* we derive the Coq prelude *)

Module Prelude.
derive Init.Datatypes.Empty_set.
derive Init.Datatypes.unit.
derive Init.Datatypes.bool.
derive Init.Datatypes.nat.
derive Init.Datatypes.option.
derive Init.Datatypes.sum.
derive Init.Datatypes.prod.
derive Init.Datatypes.list.
derive Init.Datatypes.comparison.
End Prelude.

Export Prelude.
