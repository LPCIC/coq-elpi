From elpi.apps Require Import eltac.discriminate.

Set Implicit Arguments.

Inductive foo (A : Type) | (B : Type) : nat -> Type :=
 | K : foo B 0
 | K1 : forall n, foo B n -> foo B (S n)
 | K2 : forall n, (A -> foo (B*B) n) -> foo B (n+n).

Elpi derive.isK foo.

(* Let's test a little that we are not too syntactic *)
Definition AliasK2 A B n (f : A -> foo A (B*B) n) := K2 f.
Definition AliasEQ := @eq.

Example test_discriminate (k : foo nat nat 0) (f : nat -> foo nat (nat*nat) 1) :
  AliasEQ (AliasK2 f) (K1 (K1 k)) -> K nat nat = K nat nat -> { Type = Prop } + { True = False }.
Proof.
intros H F.
Fail eltac.discriminate (F).
eltac.discriminate (H).
Qed.

Set Universe Polymorphism.
Inductive Bool := TT | FF.
Elpi derive.isK Bool.

Goal (TT = FF) -> False.
intros p.
eltac.discriminate (p).
Abort.

Inductive Nat := O' | S' : Nat -> Nat.
Elpi derive.isK Nat.

Goal forall (n : Nat), (S' n = O') -> False.
intros n p.
eltac.discriminate (p).
Abort.

Unset Universe Polymorphism.