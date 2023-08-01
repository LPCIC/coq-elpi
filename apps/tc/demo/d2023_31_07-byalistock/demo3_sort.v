From elpi.apps.tc.tests.premisesSort Require Import sortCode.
Elpi Debug "simple-compiler".

Class C1 (S : Type) (T : Type).
Class C2 (S : Type).
Class C3 (S : Type).

Global Hint Mode C1 + - : typeclass_instances.
Global Hint Mode C2 + : typeclass_instances.
Global Hint Mode C3 + : typeclass_instances.
Elpi AddAllClasses. 

Global Instance Inst1 : C1 nat nat. Qed.
Global Instance Inst2 T1 `(C1 T1 T1) : C2 T1. Qed.
Global Instance Inst3 T1 T2 `(C2 T2, C1 T1 T2) : C3 T1. Qed.

Elpi AddAllInstances.
Elpi Override TC TC_solver All.
Goal C3 nat.
  apply _.
Qed.

(* Following has a cyclic dependecy, therefore error *)
(* Global Instance C2 {S T : Type} `{A T S, B S T} : C bool. Admitted. *)
(* Elpi AddInstances C2. *)

(* Global Instance C3 {S T : Type} `{B T S} : C S. Admitted. *)
(* Elpi AddInstances C3. *)