From elpi Require Import derive.isK.
From elpi Require Import derive.projK.

Set Implicit Arguments.

(***************************************************************)

Module Test_isK.

Inductive foo (A B : Type) : nat -> Type :=
 | K : foo A B 0
 | K1 : forall n, foo A B n -> foo A B (S n)
 | K2 : forall n, (A -> foo A (B*B) n) -> foo A B (n+n).

Elpi derive.isK foo.
Fail Elpi derive.isK.

Section ctx.

Variables A B : Type.
Variable n : nat.
Variable x : foo A B n.
Variable f : A -> foo A (B*B) n.

Example test_isK : isK (K A B) = true /\ isK (K1 x) = false /\ isK (K2 f) = false.
Proof. repeat split. Qed.

Example test_isK1 : isK1 (K A B) = false /\ isK1 (K1 x) = true /\ isK1 (K2 f) = false.
Proof. repeat split. Qed.

Example test_isK2 : isK2 (K A B) = false /\ isK2 (K1 x) = false /\ isK2 (K2 f) = true.
Proof. repeat split. Qed.

End ctx.

End Test_isK.

(***************************************************************)

Module Test_projK.


Elpi derive.projK nat.

Lemma test_proj1S x : proj1S 33 (S x) = x.
Proof. split. Qed.


End Test_projK.

(***************************************************************)