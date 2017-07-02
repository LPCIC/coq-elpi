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

Elpi Accumulate File "eq.elpi".

Elpi Run "create-eq-with-proof ""nat"".".
Check nat_equal_ok.

Elpi Run "create-eq-with-proof ""mbtree"".".
Check mbtree_equal_ok.

Elpi Run "create-eq-from-name ""mlist"".".
Check mlist_equal.

Theorem mlist_equal_ok : forall (A B : Type),
  forall (eqA : A -> A -> bool) (eqB : B -> B -> bool),
  (forall (a b : A), eq_ok A eqA a b) -> 
  (forall (a b : B), eq_ok B eqB a b) ->
  (forall (a b : mlist A B), eq_ok (mlist A B) (mlist_equal A B eqA eqB) a b).
Proof. intros A B eqA eqB. unfold eq_ok. intros HeqA HeqB.
  intro a. induction a.
  - intro b'. destruct b'.
    + simpl. split.
      * intro H. apply andb_prop in H.
        destruct H. apply andb_prop in H0. destruct H0.
        apply (fg_equal (mlist A B) (mlist A B) (mcons A B a b) (mcons A B a1 b0) a0 b'
          (proj1 (iff_and (IHa b')) H)
          (fg_equal B (mlist A B -> mlist A B) (mcons A B a) (mcons A B a1) b b0
            (proj1 (iff_and (HeqB b b0)) H0)
            (fg_equal A (B -> mlist A B -> mlist A B) (mcons A B) (mcons A B) a a1
              (proj1 (iff_and (HeqA a a1)) H1)
              eq_refl
            )
          )
        ).
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
