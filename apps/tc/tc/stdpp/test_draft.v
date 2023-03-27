Require Import List Bool Arith.
Import ListNotations.

Inductive TCForall {A} (P : A -> Prop) : list A -> Prop :=
  | TCForall_nil : TCForall P []
  | TCForall_cons x xs : P x -> TCForall P xs -> TCForall P (x :: xs).
Existing Class TCForall.
Global Existing Instance TCForall_nil.
Global Existing Instance TCForall_cons.
Global Hint Mode TCForall ! ! ! : typeclass_instances.

Section Relation_Definition.

  Variable A : Type.

  Definition relation := A -> A -> Prop.
  Variable R : relation.

  Definition reflexive : Prop := forall x:A, R x x.
  Definition transitive : Prop := forall x y z:A, R x y -> R y z -> R x z.
  Definition symmetric : Prop := forall x y:A, R x y -> R y x.
  Definition antisymmetric : Prop := forall x y:A, R x y -> R y x -> x = y.

End Relation_Definition.

Class Equiv A := equiv: relation A.

Compute (equiv (fun a b => a + b)).

Lemma or_l (P Q: Prop) : not Q -> P \/ Q <-> P.
Proof.
  tauto.
  Show Proof.
Qed.


Lemma natMod4: forall (a : list nat), TCForall (fun x => x mod 4 < 4) a.
Proof.
  induction a as [| X Y].
  apply TCForall_nil.
  apply TCForall_cons.
  Search (_ mod ?x < ?x) inside Nat.
  now apply Nat.mod_upper_bound.
  all: easy.
Qed.

Goal forall x, exists x1 x2, x1 > x /\ x2 = x.
Proof.
  intros.
  exists (S x), x.
  apply (conj (le_n (S x)) eq_refl).
  (* intuition. *)
  Show Proof.
Qed.

Fixpoint last {A} (l : list A) : option A :=
  match l with [] => None | [x] => Some x | _ :: l => last l end.
Local Arguments last : simpl nomatch.

Lemma last_simpl_test_cons_cons l : last (5 :: 10 :: 11 :: l) = last (5 :: 11 :: l).
Proof. simpl. easy. Qed.

Require Import Morphisms.

Fixpoint replicate {A} (n : nat) (x : A) : list A :=
  match n with 0 => [] | S n => x :: replicate n x end.
Global Instance: Params (@replicate) 2 := {}.

(* Print HintDb typeclass_instances. *)

Inductive term : Set :=
  | zero
  | suc (t : term)
.

Fixpoint greaterThan (t t' : term) {struct t} : bool :=
  match t, t' with
   | zero, _ => false
   | suc t, zero => true
   | suc t, suc t' => t > t'
  end
where "t > t'" := (greaterThan t t').

Arguments greaterThan : simpl nomatch.

Lemma successorIsGreater : forall t : term, suc (suc t) > suc t = true.
Proof.
  induction t.
  now simpl.
  now simpl in * |- *.
Qed.

Ltac red_greaterThan :=
  match goal with
  | |- context [ suc ?n > suc ?m ] =>
    change (suc n > suc m) with (n > m)
  | |- context [ suc ?n > zero ] =>
    change (suc n > zero) with true
  | |- context [ zero > ?n ] =>
    change (zero > n) with false
  end.