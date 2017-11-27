From elpi Require Import derive.projK.

Set Implicit Arguments.

Elpi derive.projK nat.

Lemma test_proj1S x : proj1S 33 (S x) = x.
Proof. split. Qed.
