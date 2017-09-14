From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From mathcomp Require Import path choice fintype tuple finset bigop.

From elpi Require Import elpi.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope rel_scope with rel.

(***************************)
(* Heterogeneous Relations *)
(***************************)
Section hrel.

Definition sub_hrel A B (R R' : A -> B -> Type) :=
  forall (x : A) (y : B), R x y -> R' x y.

Notation "X <= Y" := (sub_hrel X%rel Y%rel) : rel_scope.

Inductive eq_hrel A B (R R' : A -> B -> Type) :=
  EqHrel of (R <= R')%rel & (R' <= R)%rel.

Notation "X <=> Y" := (eq_hrel X Y) (format "X  <=>  Y", at level 95) : rel_scope.

Lemma eq_hrelRL A B (R R' : A -> B -> Type) : (R <=> R')%rel -> (R <= R')%rel.
Proof. by case. Qed.

Lemma eq_hrelLR A B (R R' : A -> B -> Type) : (R <=> R')%rel -> (R' <= R)%rel.
Proof. by case. Qed.

Definition comp_hrel A B C
  (R : A -> B -> Type) (R' : B -> C -> Type) : A -> C -> Type :=
    fun a c => sigT (fun b => R a b * R' b c)%type.

Notation "X \o Y" := (comp_hrel X Y) : rel_scope.

Lemma comp_hrelP A B C (R : A -> B -> Type) (R' : B -> C -> Type)
  (b : B) (a : A) (c : C) : R a b -> R' b c -> (R \o R')%rel a c.
Proof. by exists b. Qed.

Definition prod_hrel A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) :
  A * B -> A' * B' -> Type :=
  fun x y => (rA x.1 y.1 * rB x.2 y.2)%type.

Lemma comp_eqr A B (R : A -> B -> Type) : (R \o eq <= R)%rel.
Proof. by move=> x y [y' [? <-]]. Qed.

Lemma comp_eql A B (R : A -> B -> Type) : (eq \o R <= R)%rel.
Proof. by move=> x y [y' [<-]]. Qed.

Definition fun_hrel A B (f : B -> A) : A -> B -> Type :=
  fun a b => f b = a.

Definition ofun_hrel A B (f : B -> option A) : A -> B -> Type :=
  fun a b => f b = Some a.

Definition hrespectful (A B C D : Type)
  (R : A -> B -> Type) (R' : C -> D -> Type) : (A -> C) -> (B -> D) -> Type :=
  fun f g => forall (x : A) (y : B), R x y -> R' (f x) (g y).

Notation " R ==> S " := (@hrespectful _ _ _ _ R%rel S%rel)
    (right associativity, at level 55) : rel_scope.

Lemma sub_hresp_comp A B C (R1 R1' : A -> B -> Prop) (R2 R2' : B -> C -> Prop) :
  (((R1 ==> R1') \o (R2 ==> R2')) <= ((R1 \o R2) ==> (R1' \o R2')))%rel.
Proof.
move=> f h [g [rfg rgh]] x z [y [rxy ryz]]; exists (g y).
by split; [apply: rfg | apply: rgh].
Qed.

End hrel.

Notation "X \o Y" := (comp_hrel X%rel Y%rel) : rel_scope.
Notation "X <= Y" := (sub_hrel X%rel Y%rel) : rel_scope.
Notation "X <=> Y" := (eq_hrel X%rel Y%rel) (format "X  <=>  Y", at level 95) : rel_scope.
Notation " R ==> S " := (@hrespectful _ _ _ _ R%rel S%rel)
    (right associativity, at level 55) : rel_scope.


Definition refines X Y (R : X -> Y -> Type) x y := R x y.
Arguments refines {_ _} R%rel _ _.

Lemma refines_apply
  {A B} {R : A -> B -> Type} 
  {C D} {R' : C -> D -> Type} :
  forall (a : A) (b : B), refines R a b ->
  forall (c : A -> C) (d : B -> D), refines (R ==> R') c d ->
   refines R' (c a) (d b).
Proof.

Admitted.



Elpi Tactic coqeal " typecheck. ".
Elpi Accumulate File "coq-EAL.elpi".
Elpi Run coqeal " typecheck ".


Section CoqEAL.

Context (N : Type).
Context (R : nat -> N -> Type).
Context (zero one : N).
Context (add : N -> N -> N).

Context `{Rzero : refines R 0 zero}.
Elpi Tactic coqeal "easy {{0}} {{@Rzero}}.".

Context `{Rone : refines R 1 one}.     
Elpi Tactic coqeal "easy {{1}} {{@Rone}}.".

Context `{Radd : refines (R ==> R ==> R)%rel addn add}.
Elpi Tactic coqeal "easy {{addn}} {{@Radd}}.".

Lemma test_refines : { x : _ & refines (R ==> R) (addn 1) x}.
Proof.
  eexists.
  elpi coqeal; shelve_unifiable.
Qed.

Lemma test_refines2 : { x : _ & refines R (addn 1 0) x}.
Proof.
  eexists.
  elpi coqeal; shelve_unifiable.
Qed.

Lemma test_refines_big : { x : N & refines R (0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + (((((((((0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + (((((((0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + (((((0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + 1)) + 1) + 1)) + 1)) + 1) + 1)))))))) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + (((((0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + 1)) + 1) + 1)) + 1)) + 1) + 1)))))))) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + 1)) + 1) + 1)) + 1)) + 1) + 1)))))))) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + (((((((0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + (((((0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + 1)) + 1) + 1)) + 1)) + 1) + 1)))))))) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + (((((0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + 1)) + 1) + 1)) + 1)) + 1) + 1)))))))) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + 1)) + 1) + 1)) + 1)) + 1) + 1)))))))) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + (((((0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + 1)) + 1) + 1)) + 1)) + 1) + 1)))))))) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + (((((0 + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + 1)) + 1) + 1)) + 1)) + 1) + 1)))))))) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + ((0 + (((((0 + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + ((0 + ((0 + 1)) + 1) + 1)) + 1)) + 1) + 1)) + 1) + 1)) + 1)) + 1) + 1))))))))%nat x}.
Proof.
  eexists.
  Time elpi coqeal; shelve_unifiable.
Qed.

End CoqEAL.

