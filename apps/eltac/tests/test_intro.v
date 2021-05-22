From elpi.apps Require Import eltac.intro.

Lemma test1 : forall x, x = 1.
Proof.
eltac.intro "a".
Abort.

Example test_intro : True -> True.
Proof.
eltac.intro x.
exact x.
Qed.

