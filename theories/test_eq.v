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
Print fg_equal.

Definition eq_ok (A : Type) (eq : A -> A -> bool) (a b : A) :=
  (eq a b = true <-> a = b).

Elpi Accumulate File "eq.elpi".
Elpi Run "create-eq-from-name ""mbtree"".".
Elpi Run "create-eq-proof-test.".
Check mbtree_equal_ok.

Definition test :=
  fun (x0 : forall (A : Type), A -> A -> bool)
      (x1 : forall (A : Type) (a b : A), x0 A a b = true)
      (x2 : forall (A : Type) (a b : A), eq_ok A (x0 A) a b)
      (x3 x4 x5 x6 : mbtree) (x7 x8 : nat) =>
  fg_equal nat mbtree (mbnode x3 x5) (mbnode x4 x6) x7 x8
    (proj1 (iff_and (x2 nat x7 x8)) (x1 nat x7 x8))
    (fg_equal mbtree (nat -> mbtree) (mbnode x3) (mbnode x4) x5 x6
      (proj1 (iff_and (x2 mbtree x5 x6)) (x1 mbtree x5 x6))
      (fg_equal mbtree (mbtree -> nat -> mbtree) mbnode mbnode x3 x4
        (proj1 (iff_and (x2 mbtree x3 x4)) (x1 mbtree x3 x4))
        eq_refl
      )
    ).
Print test.
Print iff.
Print iff_and.
Locate "_ <-> _".
Check test.
Elpi Run "coq-locate ""test"" Test, Test = const GR,
  coq-env-const GR Bo TBo,
  coq-say Bo.".

Elpi Run "create-eq-from-name ""mbtree"".".
Check mbtree_equal.

Theorem mbtree_equal_ok : forall (eq_nat : nat -> nat -> bool)
  (eq_prod : nat * nat -> nat * nat -> bool),
  (forall (a b : nat), eq_ok nat eq_nat a b) ->
  (forall (a b : nat * nat), eq_ok (nat * nat) eq_prod a b) ->
  (forall (a b : mbtree), eq_ok mbtree (mbtree_equal eq_nat eq_prod) a b).
Proof.
  unfold eq_ok. intros eqn eqp Heqn Heqp a. induction a.
  - intro b. destruct b.
    + simpl. split.
      * intro H.
        apply andb_prop in H. destruct H.
        apply andb_prop in H0. destruct H0.
        apply (fg_equal nat mbtree (mbnode a1 a2) (mbnode b1 b2)
          n n0 (proj1 (iff_and (Heqn n n0)) H)
            (fg_equal mbtree (nat -> mbtree)
            (mbnode a1) (mbnode b1) a2 b2 (proj1 (iff_and (IHa2 b2)) H0)
              (fg_equal mbtree (mbtree -> nat -> mbtree)
              mbnode mbnode a1 b1 (proj1 (iff_and (IHa1 b1)) H1)
              eq_refl)
            )
          ).
      * intro H.
        apply (andb_true_intro (conj
          (proj2 (iff_and (Heqn n n0)) (@f_equal mbtree nat (fun m => match m with
                             | mbnode _ _ n => n
                             | mbleaf _     => n
                    end) (mbnode a1 a2 n) (mbnode b1 b2 n0) H))
          (andb_true_intro (conj
            (proj2 (iff_and (IHa2 b2)) (@f_equal mbtree mbtree (fun m => match m with
                | mbnode _ n _ => n
                | mbleaf _     => a2
              end) (mbnode a1 a2 n) (mbnode b1 b2 n0) H))
            (proj2 (iff_and (IHa1 b1)) (@f_equal mbtree mbtree (fun m => match m with
                | mbnode n _ _ => n
                | mbleaf _     => a2
              end) (mbnode a1 a2 n) (mbnode b1 b2 n0) H))
          ))
        )).
    + simpl. split.
      * intro H. discriminate H.
      * intro H. discriminate H.
  - intro b. destruct b.
    + simpl. split.
      * intro H. discriminate H.
      * intro H. discriminate H.
    + simpl. split.
      * intro H.
        apply (fg_equal (nat * nat) mbtree mbleaf mbleaf p p0
                (proj1 (iff_and (Heqp p p0)) H)
                eq_refl
              ).
      * intro H.
        apply (proj2 (iff_and (Heqp p p0)) (@f_equal mbtree (nat*nat) (fun m => match m with
            | mbnode _ _ _ => p
            | mbleaf n => n
            end) (mbleaf p) (mbleaf p0) H)).
Qed.
Print mbtree_equal_ok.

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

Check @eq_ind.

Elpi Run "create-eq-from-name ""mlist"".".
Check mlist_equal.
Elpi Accumulate "
  eq-function {{mlist}} {{mlist_equal}}.
".

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
Check mlist_ind.
Print mlist_equal_ok.;
Check @False_ind.
Elpi Run "coq-locate ""mlist_equal_ok"" P, P = const GR,
  coq-env-const GR Bo Ty, coq-say Bo.".
Check @conj.
Check eq_ok.
Check and.
Check awful_ind.
Check list_ind.
Check @eq_ind.
Check andb_true_intro.
Check andb_prop.

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
