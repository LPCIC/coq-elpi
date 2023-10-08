From elpi.apps.tc.tests.premisesSort Require Import sortCode.
Elpi Debug "simple-compiler".

Class A (S : Type) (T : Type).
Class B (S : Type) (T : Type).
Class C (S : Type).

Global Hint Mode A + - : typeclass_instances.
Global Hint Mode B + - : typeclass_instances.
Elpi AddAllClasses. 

Global Instance A1 : A nat nat. Admitted.
Global Instance B1 : B nat nat. Admitted.

Global Instance C1 {S T : Type} `{B S T, A T S} : C T. Admitted.

Elpi AddAllInstances.
Elpi Override TC TC_solver All.
Goal C nat.
  apply _.
Qed.

(* Following has a cyclic dependecy, therefore error *)
(* Global Instance C2 {S T : Type} `{A T S, B S T} : C bool. Admitted. *)
(* Elpi AddInstances C2. *)

(* Global Instance C3 {S T : Type} `{B T S} : C S. Admitted. *)
(* Elpi AddInstances C3. *)