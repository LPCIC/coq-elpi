From elpi.apps.tc.tests.premisesSort Require Import sortCode.
Elpi Debug "simple-compiler".
Set TC AddModes.

Class A (S : Type).
Class B (S : Type).
Class C (S : Type).

Global Hint Mode A + : typeclass_instances.

Global Instance A1 : A nat. Admitted.

Global Instance B1 : B nat. Admitted.

(* 
  Here since the output of T is input in A, we want to reorder
  the goals such that the proof of be is computed first.
  Question do we want to raise an error or try to rearrange 
  subgoals in C1. We can try to make an analysis in the compiling
  phase to raise the error.
*)
Global Instance C1 {T : Type} `{e : A T, B T} : C bool. Admitted.

Elpi AddAllClasses. 
Elpi AddAllInstances.

Elpi TC Solver Override TC.Solver All.

Elpi Print TC.Solver "elpi.apps.tc.tests/TC.Solver".
Goal C bool.
  apply _.
Qed.
