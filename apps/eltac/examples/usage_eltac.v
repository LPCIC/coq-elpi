From elpi.apps Require Import derive.
From elpi.apps Require Import eltac.tactics.

derive nat.

Lemma example : forall x y : nat, S x = S y -> 0 = 1 -> False.
Proof.
intros x y I D.
eltac.injection I.
simpl. intros E.
eltac.discriminate D.
Qed.