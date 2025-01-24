From elpi.apps Require Import eltac.apply.
Goal (forall (x y : nat), x + y = y + x) -> (forall y, 3 + y = y + 3).
Proof.
    intro H.
    eltac.apply H.
Qed.

Goal (3 + 4 = 4 + 3).
Proof.
    eltac.apply PeanoNat.Nat.add_comm.
Qed.