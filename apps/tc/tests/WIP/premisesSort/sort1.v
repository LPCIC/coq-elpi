From elpi.apps.tc.tests.premisesSort Require Import sortCode.

Set Warnings "+elpi".
Class A (S : Type).
Class B (S : Type).
Class C (S : Type).

Elpi Trace Browser.
Global Instance A1 : A nat. Admitted.
Global Instance A2 : A bool. Admitted.

Global Instance B1 : B nat. Admitted.

Global Instance C1 {T : Type} `{A T, B T} : C bool. Admitted.

(* Simpl example where we do backtrack *)
Goal C bool.
  apply _.
Qed.