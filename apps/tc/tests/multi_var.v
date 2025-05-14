From elpi Require Import elpi tc.

Class C (T : Type) : Type := {}.
Axiom t : forall n m : nat, Type.

Instance tC (n : nat) : C (t n n). Qed.
Set Printing All.
Goal C (t 0 0). apply _. Qed.

Instance tC1 (n : nat) : let n' := n in C (t n n'). Qed. 

Goal C (t 0 (id 0)). apply _. Qed.

(* Elpi Print TC.Solver "elpi.apps.tc.examples/TC.Solver". *)
