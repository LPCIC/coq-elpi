From elpi Require Import elpi.
Elpi Init "./" "./elpi/".

Elpi Accumulate File "pervasives.elpi".


Require Import Coq.Lists.List.

Inductive mbtree :=
| mbnode : mbtree -> mbtree -> nat -> mbtree
| mbleaf : nat * nat -> mbtree.

Fixpoint eq_nat (n m : nat) :=
  match n with
  | O   => match m with
           | O   => true
           | S _ => false
           end
  | S x => match m with
           | O   => false
           | S y => eq_nat x y
           end
  end.

Definition tmp (f : nat -> nat -> bool)
(a b : mbtree) := true.

Definition tmp' (f : list nat -> list nat -> bool)
(a b : mbtree) := true.

Fixpoint eq_list (A : Type)
(eq : A -> A -> bool) (l1 l2 : list A) :=
match (l1,l2) with
| (cons x1 t1, cons x2 t2) => andb (eq x1 x2)
                         (eq_list A eq t1 t2)
| (nil,nil) => true
| _ => false
end.

Inductive awful (A B : Type) : Type :=
| mkawful : awful (list B) B -> awful A B
| awful_nil : B -> awful A B.

Inductive mlist (A B : Type) : Type :=
| mcons : A -> B -> mlist A B -> mlist A B
| mnil  : mlist A B.
About mlist.

Theorem fg_equal :
  forall (A B : Type) (f g : A -> B) (x y : A),
    x = y -> f = g -> f x = g y.
Proof.
  intros A B f g x y Hxy Hfg.
  rewrite <- Hxy. rewrite <- Hfg.
  reflexivity.
Qed.

Definition eq_ok (A : Type) (eq : A -> A -> bool) (a b : A) :=
  (eq a b = true <-> a = b).

Module DecEq.
  Record class (T : Type) := Class { cmp : T -> T -> bool;
                                     proof : forall (a b : T), cmp a b = true <-> a = b }.
  Structure type := Pack { obj : Type; class_of : class obj }.
  Definition op (e : type) : obj e -> obj e -> bool :=
    let 'Pack _ (Class _ cmp _) := e in cmp.
  Definition op_ok (e : type) : forall (a b : obj e), op e a b = true <-> a = b :=
    let 'Pack _ (Class _ _ proof) := e in proof.
  Arguments op {e} x y : simpl never.
  Arguments op_ok {e} : simpl never.
  Arguments Class {T} cmp proof.
  Module theory.
    Notation "x ~~ y" := (op x y) (at level 70).
  End theory.
End DecEq.

Elpi Accumulate File "eq.elpi".

Elpi Run "derive-deceq ""prod"".".
Fail Elpi Run "create-eq-with-proof ""mbtree"".".
Elpi Run "derive-deceq ""nat"".".
Elpi Run "derive-deceq ""mbtree"".".

