From elpi Require Import derive.param2.

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

