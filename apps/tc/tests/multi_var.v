From elpi Require Import tc.

Module let_by_hand.
Class C (T : Type) : Type := {}.
Axiom t : forall n m : nat, Type.

Instance tC (n : nat) : C (t n n). Qed.
Goal C (t 0 0). apply _. Qed.

Instance tC1 (n : nat) : let n' := n in C (t n n'). Qed. 

Goal C (t 0 (id 0)). apply _. Qed.
End let_by_hand.

Module let_programmatic.
Class C (T : Type) : Type := {}.
Axiom t : forall n m : nat, Type.

Elpi TC.Pending_lettify.
(* Same as tC1 in previous module, but lettified programmatically  *)
Instance tC1 (n : nat) : C (t n n). Qed.

Goal C (t 0 0). apply _. Qed.

Goal C (t 0 (id 0)). apply _. Qed.
End let_programmatic.




(* Elpi Print TC.Solver "elpi.apps.tc.examples/TC.Solver". *)
