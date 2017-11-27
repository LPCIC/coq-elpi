From elpi Require Import derive.param1.

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
