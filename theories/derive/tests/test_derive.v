From elpi Require Import derive.isK.
From elpi Require Import derive.projK.
From elpi Require Import derive.eq.
From elpi Require Import derive.param1.
From elpi Require Import derive.param2.

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

Module Test_eq.

Elpi derive.eq nat.
Elpi derive.eq list.

End Test_eq.

(***************************************************************)

Module Test_param1.

Unset Implicit Arguments.

Elpi derive.param1 unit unitP.
Elpi derive.param1 nat natP.

Inductive fin : nat -> Type :=
    FO : fin 0 | FS : forall n : nat, fin n -> fin (S n).
Elpi derive.param1 fin finP.
 
Fixpoint fin_length  n (v : fin n) :=
  match v with FO => 0 | FS _ w => S (fin_length _ w) end.

Elpi derive.param1 fin_length fin_lengthP.

Inductive vec (A : Type) : nat -> Type :=
    nil : vec A 0 | cons : A -> forall n : nat, vec A n -> vec A (S n).
Elpi derive.param1 vec vecP.

Fixpoint vec_length (A : Type) n (v : vec A n) :=
  match v with nil _ => 0 | cons _ _ _ w => S (vec_length _ _ w) end.
Elpi derive.param1 vec_length vec_lengthP.
Elpi derive.param1 list listP.
Elpi derive.param1 listP listPP.
Elpi derive.param1 eq eqP.

Fixpoint plus' m n := match n with 0 => m | S n => S (plus' m n) end.
Elpi derive.param1 plus' plus'P.
Elpi derive.param1 plus plusP.
Elpi derive.param1 prod prodP.
Elpi derive.param1 fst fstP.
Elpi derive.param1 snd sndP.
Elpi derive.param1 Nat.divmod divmodP.
Elpi derive.param1 Nat.div divP.

Definition test m n p q r := m + n + p + q + r.
Elpi derive.param1 test testP.

Definition vec_length_type := forall (A : Type) (n : nat), vec A n -> nat.

Elpi derive.param1 vec_length_type vec_length_typeP.

Definition vec_length_rec (vec_length : vec_length_type)
  (A : Type) n (v : vec A n) :=
  match v with nil _ => 0 | cons _ _ _ w => S (vec_length _ _ w) end.
Elpi derive.param1 vec_length_rec vec_length_recP.

Elpi Query derive.param1 "with-TC-reali (reali {{O}} Y)".
Elpi Query derive.param1 "with-TC-reali (reali {{S (S 0)}} Y)".
Elpi Query derive.param1 "with-TC {{@reali_db}} retrieve-reali (reali {{nat}} Y)".

Definition nat2nat := nat -> nat.
Definition nat2nat2nat := nat -> nat -> nat.
Elpi derive.param1 nat2nat nat2natP.
Elpi derive.param1 nat2nat2nat nat2nat2natP.
Elpi derive.param1 pred predP.

Print predP.
Check (predP : nat2natP pred).

Fixpoint predn n := match n with 0 => 0 | S n => S (predn n) end.

Elpi derive.param1 predn prednP.

Check (prednP : nat2natP predn).
Check (plusP : nat2nat2natP plus).

Fixpoint quasidn n m := S (match n with 0 => m | S n => S (quasidn n m) end).
Elpi Query derive.param1 "reali-const {{@quasidn}} _ _ XP _".

Fixpoint weirdn n := match n with S (S n) => S (weirdn n) | _ => 0 end.
Elpi Query derive.param1 "reali-const {{@weirdn}} _ _ XP _".

Inductive bla : nat -> Type := Bla : nat -> bla 0 | Blu n : bla n -> bla 1.
Elpi derive.param1 bla blaP.

Elpi Query derive.param1 "coq-TC-db-for {term->gr {{@reali_db}}} PDb".

Fixpoint silly (n : nat) := n.
Elpi derive.param1 silly sillyP.

End Test_param1.

(***************************************************************)

Module Test_param2.

Unset Implicit Arguments.

Elpi derive.param2 unit unitR.
Elpi derive.param2 nat natR.

Inductive fin : nat -> Type :=
    FO : fin 0 | FS : forall n : nat, fin n -> fin (S n).
Elpi derive.param2 fin finR.

Fixpoint fin_length  n (v : fin n) :=
  match v with FO => 0 | FS _ w => S (fin_length _ w) end.
Elpi derive.param2 fin_length fin_lengthR.

Inductive vec (A : Type) : nat -> Type :=
    nil : vec A 0 | cons : A -> forall n : nat, vec A n -> vec A (S n).
Elpi derive.param2 vec vecR.

Fixpoint vec_length (A : Type) n (v : vec A n) :=
  match v with nil _ => 0 | cons _ _ _ w => S (vec_length _ _ w) end.
Elpi derive.param2 vec_length vec_lengthR.
Elpi derive.param2 list listR.
Elpi derive.param2 listR listRR.
Elpi derive.param2 eq eqR.

Fixpoint plus' m n := match n with 0 => m | S n => S (plus' m n) end.
Elpi derive.param2 plus' plus'R.
Elpi derive.param2 plus plusR.
Elpi derive.param2 prod prodR.
Elpi derive.param2 fst fstR.
Elpi derive.param2 snd sndR.
Elpi derive.param2 Nat.divmod divmodR.
Elpi derive.param2 Nat.div divR.

Definition test m n p q r := m + n + p + q + r.
Elpi derive.param2 test testR.

Definition vec_length_type := forall (A : Type) (n : nat), vec A n -> nat.

Elpi derive.param2 vec_length_type vec_length_typeR.

Definition vec_length_rec (vec_length : vec_length_type)
  (A : Type) n (v : vec A n) :=
  match v with nil _ => 0 | cons _ _ _ w => S (vec_length _ _ w) end.
Elpi derive.param2 vec_length_rec vec_length_recR.

Elpi Query derive.param2 "with-TC-param (param {{O}} X Y)".
Elpi Query derive.param2 "with-TC-param (param {{S (S 0)}} X Y)".
Elpi Query derive.param2 "with-TC {{@param_db}} retrieve-param (param {{nat}} X Y)".

Definition nat2nat := nat -> nat.
Definition nat2nat2nat := nat -> nat -> nat.
Elpi derive.param2 nat2nat nat2natR.
Elpi derive.param2 nat2nat2nat nat2nat2natR.
Elpi derive.param2 pred predR.

Print predR.
Check (predR : nat2natR pred pred).

Fixpoint predn n := match n with 0 => 0 | S n => S (predn n) end.

Elpi derive.param2 predn prednR.

Check (prednR : nat2natR predn predn).
Check (plusR : nat2nat2natR plus plus).

Fixpoint quasidn n m := S (match n with 0 => m | S n => S (quasidn n m) end).
Elpi Query derive.param2 "param-const {{@quasidn}} _ _ _ _ XR _".

Fixpoint weirdn n := match n with S (S n) => S (weirdn n) | _ => 0 end.
Elpi Query derive.param2 "param-const {{@weirdn}} _ _ _ _ XR _".

Inductive bla : nat -> Type := Bla : nat -> bla 0 | Blu n : bla n -> bla 1.
Elpi derive.param2 bla blaR.

Elpi Query derive.param2 "coq-TC-db-for {term->gr {{@param_db}}} PDb".

Fixpoint silly (n : nat) := n.
Elpi derive.param2 silly sillyR.


End Test_param2.

(***************************************************************)

