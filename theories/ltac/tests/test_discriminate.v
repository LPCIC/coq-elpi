From elpi Require Import elpi.
From elpi Require Import ltac.discriminate.
From elpi Require Import ltac.injection.

Set Implicit Arguments.

Inductive foo (A B : Type) : nat -> Type :=
 | K : foo A B 0
 | K1 : forall n, foo A B n -> foo A B (S n)
 | K2 : forall n, (A -> foo A (B*B) n) -> foo A B (n+n).

Elpi derive.isK foo.

(* Let's test a little that we are not too syntactic *)
Definition AliasK2 A B n (f : A -> foo A (B*B) n) := K2 f.
Definition AliasEQ := @eq.

Example test_discriminate (k : foo nat nat 0) (f : nat -> foo nat (nat*nat) 1) :
  AliasEQ (AliasK2 f) (K1 (K1 k)) -> K nat nat = K nat nat -> { Type = Prop } + { True = False }.
Proof.
intros H F.
Fail elpi discriminate (F).
elpi discriminate (H).
Show Proof.
Qed.


