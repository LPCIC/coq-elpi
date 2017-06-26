From elpi Require Import elpi.
Elpi Init "./" "./elpi/".

Elpi Accumulate File "pervasives.elpi".
Elpi Accumulate File "coq-lib.elpi".

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

Inductive awful A B :=
| mkawful : awful (list B) B -> awful A B
| awful_nil : B -> awful A B.

Inductive mlist A B :=
| mcons : A -> B -> mlist A B -> mlist A B
| mnil  : mlist A B.

Elpi Accumulate File "eq.elpi".

Elpi Run "create-eq-from-name ""prod"".".
Elpi Accumulate "
  eq-function {{prod}} {{prod_equal}}.
".

Elpi Run "create-eq-from-name ""nat"".".
Elpi Accumulate "
  eq-function {{nat}} {{nat_equal}}.
".

Theorem nat_equal_ok : forall (a b : nat),
  (nat_equal a b = true <-> a = b).
Proof.
  intro a. induction a as [| a' IH ].
  - intro b. destruct b.
    + simpl. split.
      * intro. reflexivity.
      * intro. reflexivity.
    + simpl. split.
      * intro H. discriminate H.
      * intro H. discriminate H.
  - intro b. destruct b.
    + simpl. split.
      * intro H. discriminate H.
      * intro H. discriminate H.
    + simpl. split.
      * intro H. apply (f_equal S ((proj1 (iff_and (IH b))) H)).
      * intro H. apply ((proj2 (iff_and (IH b))) (f_equal pred H)).
Qed.

Elpi Run "create-eq-from-name ""mbtree"".".
Elpi Accumulate "
  eq-function {{mbtree}} {{mbtree_equal}}.
".
Check mbtree_equal.
Compute (mbtree_equal
  (mbnode (mbleaf (1,2))
          (mbnode (mbleaf (3,4)) (mbleaf (5,6)) 7)
          8
  )
  (mbnode (mbleaf (1,2))
          (mbnode (mbleaf (4,4)) (mbleaf (5,6)) 7)
          8
  )
).

Check @f_equal.

Theorem fg_equal :
  forall (A B : Type) (f g : A -> B) (x y : A),
    f = g -> x = y -> f x = g y.
Proof.
  intros A B f g x y Hfg Hxy.
  rewrite <- Hxy. rewrite <- Hfg.
  reflexivity.
Qed.
Print fg_equal.
Check @eq_ind.

Elpi Run "create-eq-from-name ""mlist"".".
Check mlist_equal.
Elpi Accumulate "
  eq-function {{mlist}} {{mlist_equal}}.
".

Check mlist_equal.
Definition eq_ok {A : Type} (eq : A -> A -> bool) := forall (a b : A),
  (eq a b = true <-> a = b).
Theorem mlist_equal_ok : forall (A B : Type),
  forall (eqA : A -> A -> bool) (eqB : B -> B -> bool),
  eq_ok eqA -> eq_ok eqB -> eq_ok (mlist_equal A B eqA eqB).
Proof. intros A B eqA eqB. unfold eq_ok. intros HeqA HeqB.
  intro a. induction a.
  - intro b'. destruct b'.
    + simpl. split.
      * intro H. apply andb_prop in H.
        destruct H. apply andb_prop in H0. destruct H0.
        apply (proj1 (iff_and (HeqA a a1))) in H1.
        apply (proj1 (iff_and (HeqB b b0))) in H0.
        apply (proj1 (iff_and (IHa b'))) in H.
        apply (@eq_trans (mlist A B)
        (mcons A B a b a0) (mcons A B a b b') (mcons A B a1 b0 b')
        ((@f_equal (mlist A B) (mlist A B) (mcons A B a b) a0 b') H)
        (
          (@f_equal (mlist A B -> mlist A B) (mlist A B)
                        (fun f => f b') (mcons A B a b) (mcons A B a1 b0)) (
              (@eq_trans (mlist A B -> mlist A B)
              (mcons A B a b) (mcons A B a b0) (mcons A B a1 b0)
              ((@f_equal B (mlist A B -> mlist A B) (mcons A B a) b b0) H0)
              (@f_equal (B -> mlist A B -> mlist A B) (mlist A B -> mlist A B)
                        (fun f => f b0) (mcons A B a) (mcons A B a1)
                        ((@f_equal A (B -> mlist A B -> mlist A B) (mcons A B) a a1) H1)))
        ))).
      * intro H. apply andb_true_intro. split.
{
apply ((proj2 (iff_and (IHa b')))
      ((@f_equal (mlist A B) (mlist A B) (fun x => match x with
    | mcons _ _ a b m => m
    | mnil  _ _       => mnil A B
    end) (mcons A B a b a0) (mcons A B a1 b0 b')
  ) H)).
}
{ apply andb_true_intro. split. {
apply ((proj2 (iff_and (HeqB b b0)))
      ((@f_equal (mlist A B) B (fun x => match x with
  | mcons _ _ a b m => b
  | mnil  _ _       => b
  end) (mcons A B a b a0) (mcons A B a1 b0 b')
  ) H)).
}{
apply ((proj2 (iff_and (HeqA a a1)))
      ((@f_equal (mlist A B) A (fun x => match x with
  | mcons _ _ a b m => a
  | mnil  _ _       => a
  end) (mcons A B a b a0) (mcons A B a1 b0 b')
  ) H)).
}}
    + simpl. split.
      * intro H. discriminate H.
      * intro H. discriminate H.
  - destruct b.
    + simpl. split.
      * intro H. discriminate H.
      * intro H. discriminate H.
    + simpl. split.
      * intro. reflexivity.
      * intro. reflexivity.
Qed.
Check mlist_ind.
Print mlist_equal_ok.

Elpi Run "create-eq-from-name ""list"".".
Check list_equal.
Elpi Accumulate "
  eq-function {{list}} {{list_equal}}.
".
Check (list_equal nat nat_equal).
Compute (list_equal nat nat_equal
  (1::2::3::4::5::6::7::nil)
  (1::2::3::4::5::6::7::nil)
).
Compute (list_equal nat nat_equal
  (1::2::3::4::5::6::7::nil)
  (1::2::3::4::5::6::6::nil)
).

Elpi Run "create-eq-from-name ""awful"".".
Check awful_equal.
Elpi Accumulate "
  eq-function {{awful}} {{awful_equal}}.
".

Inductive FingerTree A :=
| ft_leaf : FingerTree A
| ft_node : A -> FingerTree A -> FingerTree (prod A A)
         -> FingerTree A.
Elpi Run "create-eq-from-name ""FingerTree"".".
Check FingerTree_equal.


(* Problematic examples *)
Inductive tpfn A :=
| tpfn1 : (A -> tpfn A) -> tpfn A
| tpfn2 : A -> tpfn A.
Elpi Run "create-eq-from-name ""tpfn"".".
Check tpfn_equal.

Theorem bla : 0 = 1 -> False.
Proof. intro H. discriminate H. Qed.

Check @eq_ind.
Print bla.
Check @f_equal.
Check @list_ind.

Inductive specific A :=
| sp_prod : specific A -> specific A -> specific (prod A A)
| sp_init : A -> specific A.
Elpi Run "create-eq-from-name ""specific"".".
Check specific_equal.
