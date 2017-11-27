From elpi Require Import elpi.
From elpi Require Import ltac.discriminate.
From elpi Require Import ltac.injection.

Set Implicit Arguments.

Elpi derive.projK nat.

Lemma test (a b :nat) : S a = S b -> a = b.
Proof.
intro H.
elpi injection (H).
intro I.
exact I.
Qed.
