From elpi Require Import compiler.
Elpi Debug "simple-compiler".
Set AddModes.

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
Global Instance C1 {T : Type} `{A T, B T} : C bool. Admitted.

Elpi Override TC TC_solver All.
Elpi AddAllClasses. 
Elpi AddAllInstances.

Goal C bool.
  (* TODO: here should not fail if we reorder premises of C1 *)
  Fail apply _.
Abort.