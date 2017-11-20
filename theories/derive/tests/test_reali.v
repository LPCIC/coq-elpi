(* Set Universe Polymorphism. *)

From elpi Require Import elpi.

Class reali_db {X XR : Type} (x : X) (xR : XR) := store_reali {}.
Class reali {X : Type} {XR : X -> Type} (x : X) (xR : XR x) := Reali {}.

Elpi Tactic reali.
Elpi Accumulate File "coq-extra.elpi".
Elpi Accumulate File "coq-reali.elpi".
Elpi Typecheck reali.

Elpi Print reali "reali.html"
  "pervasives.elpi"
  "coq-lib.elpi"
  "lp-lib.elpi"
  "coq-refiner.elpi".

Elpi reali unit unitP.
Elpi reali nat natP.

Inductive fin : nat -> Type :=
    FO : fin 0 | FS : forall n : nat, fin n -> fin (S n).
Elpi reali fin finP.

Fixpoint fin_length  n (v : fin n) :=
  match v with FO => 0 | FS _ w => S (fin_length _ w) end.
Elpi reali fin_length fin_lengthP.

Inductive vec (A : Type) : nat -> Type :=
    nil : vec A 0 | cons : A -> forall n : nat, vec A n -> vec A (S n).
Elpi reali vec vecP.

Fixpoint vec_length (A : Type) n (v : vec A n) :=
  match v with nil _ => 0 | cons _ _ _ w => S (vec_length _ _ w) end.
Elpi reali vec_length vec_lengthP.
Elpi reali list listP.
Elpi reali listP listPP.
Elpi reali eq eqP.

Fixpoint plus' m n := match n with 0 => m | S n => S (plus' m n) end.
Elpi reali plus' plus'P.
Elpi reali plus plusP.
Elpi reali prod prodP.
Elpi reali fst fstP.
Elpi reali snd sndP.
Elpi reali Nat.divmod divmodP.
Elpi reali Nat.div divP.

Definition test m n p q r := m + n + p + q + r.
Elpi reali test testP.

Definition vec_length_type := forall (A : Type) (n : nat), vec A n -> nat.

Elpi reali vec_length_type vec_length_typeP.

Definition vec_length_rec (vec_length : vec_length_type)
  (A : Type) n (v : vec A n) :=
  match v with nil _ => 0 | cons _ _ _ w => S (vec_length _ _ w) end.
Elpi reali vec_length_rec vec_length_recP.

Elpi Query reali "with-TC-reali (reali {{O}} Y)".
Elpi Query reali "with-TC-reali (reali {{S (S 0)}} Y)".
Elpi Query reali "with-TC {{@reali_db}} retrieve-reali (reali {{nat}} Y)".

Definition nat2nat := nat -> nat.
Definition nat2nat2nat := nat -> nat -> nat.
Elpi reali nat2nat nat2natP.
Elpi reali nat2nat2nat nat2nat2natP.
Elpi reali pred predP.

Print predP.
Check (predP : nat2natP pred).

Fixpoint predn n := match n with 0 => 0 | S n => S (predn n) end.

Elpi reali predn prednP.

Check (prednP : nat2natP predn).
Check (plusP : nat2nat2natP plus).

Fixpoint quasidn n m := S (match n with 0 => m | S n => S (quasidn n m) end).
Elpi Query reali "reali-const {{@quasidn}} _ _ XP _".

Fixpoint weirdn n := match n with S (S n) => S (weirdn n) | _ => 0 end.
Elpi Query reali "reali-const {{@weirdn}} _ _ XP _".

Inductive bla : nat -> Type := Bla : nat -> bla 0 | Blu n : bla n -> bla 1.
Elpi reali bla blaP.

Elpi Query reali "coq-TC-db-for {term->gr {{@reali_db}}} PDb".

Fixpoint silly (n : nat) := n.
Elpi reali silly sillyP.


