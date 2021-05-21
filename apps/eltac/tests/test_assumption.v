From elpi.apps Require Import eltac.assumption.

Lemma test1 x (H : x = 0) : x = 0.
Proof.
eltac.assumption.
Qed.

Example test_assumption : True -> True.
Proof.
intro x.
eltac.assumption.
Qed.


