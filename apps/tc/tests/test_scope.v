From elpi Require Import tc.

Section M.
Class C (i : Type -> Type).

Context (Q : Type -> Type).

Goal C Q ->  exists (T : Type -> Type), forall R, C R -> C (T).
  eexists.
  intros.
  Set Printing Existential Instances.
  assert (C Q) by auto.
  (* Elpi Trace Browser. *)
  apply _.
  Show Proof.
Abort.
End M.