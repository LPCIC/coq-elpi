From elpi.apps Require Import tc.

Class C.

Instance T (n:nat) : C := {}.

Elpi TC Solver Deactivate TC.Solver.


(* THIS IS COQ *)
Goal C.
  Fail apply _.
  eapply _.
  Show.
  Unshelve.
  Show.
  apply (T   2).
Qed.

(* THIS IS ELPI *)
Goal C.
  Fail apply _.
  eapply _.
  Show.
  Unshelve.
  Show.
  apply (T   2).
Qed.
