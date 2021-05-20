From elpi.apps Require Import derive.
From elpi.apps Require Import eltac.tactics.

derive nat.

Lemma example : forall x y : nat, S x = S y -> 0 = 1 -> False.
Proof.
eltac.intro "x".
eltac.intro "y".
eltac.intro "I".
eltac.intro "D".
eltac.injection I.
eltac.intro "E".
eltac.clear E.
eltac.discriminate D.
Qed.