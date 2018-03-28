From elpi Require Import derive.projK.

Set Implicit Arguments.

Elpi derive.projK nat.

Lemma test_proj1S x : projS1 33 (S x) = x.
Proof. split. Qed.
