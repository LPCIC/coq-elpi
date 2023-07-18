From elpi.apps.tc.tests.premisesSort Require Import sortCode.

Class A (S : Type).
Class B (S : Type).
Class C (S : Type).

Global Instance A1 : A nat. Admitted.
Global Instance A2 : A bool. Admitted.

Global Instance B1 : B nat. Admitted.

Global Instance C1 {T : Type} `{A T, B T} : C bool. Admitted.

(* Simpl example where we do backtrack *)
Goal C bool.
  apply _.
Qed.