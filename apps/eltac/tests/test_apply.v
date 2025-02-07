From elpi.apps Require Import eltac.apply.
Goal (forall (x y : nat), x + y = y + x) -> (forall y, 3 + y = y + 3).
Proof.
    intro H.
    eltac.apply H.
Qed.

Axiom add_comm : forall x y, x + y = y + x.

Goal (3 + 4 = 4 + 3).
Proof.
    eltac.apply add_comm.
Qed.
