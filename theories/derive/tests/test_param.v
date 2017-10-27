(* Set Universe Polymorphism. *)

From elpi Require Import elpi.

Class param_db {X X1 XR : Type} (x : X) (x : X1) (xR : XR) := store_param {}.
Class param {X : Type} {XR : X -> X -> Type} (x : X) (xR : XR x x) := Param {}.

Elpi Tactic param " typecheck.".
Elpi Accumulate File "coq-extra.elpi".
Elpi Accumulate File "coq-param.elpi".
Elpi Query param "typecheck".

Elpi Print param "param.html"
  "pervasives.elpi"
  "coq-lib.elpi"
  "lp-lib.elpi"
  "coq-refiner.elpi".

Elpi param unit unitR.
Elpi param nat natR.

Inductive fin : nat -> Type :=
    FO : fin 0 | FS : forall n : nat, fin n -> fin (S n).
Elpi param fin finR.

Fixpoint fin_length  n (v : fin n) :=
  match v with FO => 0 | FS _ w => S (fin_length _ w) end.
Elpi param fin_length fin_lengthR.

Inductive vec (A : Type) : nat -> Type :=
    nil : vec A 0 | cons : A -> forall n : nat, vec A n -> vec A (S n).
Elpi param vec vecR.

Fixpoint vec_length (A : Type) n (v : vec A n) :=
  match v with nil _ => 0 | cons _ _ _ w => S (vec_length _ _ w) end.
Elpi param vec_length vec_lengthR.
Elpi param list listR.
Elpi param listR listRR.
Elpi param eq eqR.

Fixpoint plus' m n := match n with 0 => m | S n => S (plus' m n) end.
Elpi param plus' plus'R.
Elpi param plus plusR.
Elpi param prod prodR.
Elpi param fst fstR.
Elpi param snd sndR.
Elpi param Nat.divmod divmodR.
Elpi param Nat.div divR.

Definition test m n p q r := m + n + p + q + r.
Elpi param test testR.

Definition vec_length_type := forall (A : Type) (n : nat), vec A n -> nat.

Elpi param vec_length_type vec_length_typeR.

Definition vec_length_rec (vec_length : vec_length_type)
  (A : Type) n (v : vec A n) :=
  match v with nil _ => 0 | cons _ _ _ w => S (vec_length _ _ w) end.
Elpi param vec_length_rec vec_length_recR.

Elpi Query param "with-TC-param (param {{O}} X Y)".
Elpi Query param "with-TC-param (param {{S (S 0)}} X Y)".
Elpi Query param "with-TC {{@param_db}} retrieve-param (param {{nat}} X Y)".

Definition nat2nat := nat -> nat.
Definition nat2nat2nat := nat -> nat -> nat.
Elpi param nat2nat nat2natR.
Elpi param nat2nat2nat nat2nat2natR.
Elpi param pred predR.

Print predR.
Check (predR : nat2natR pred pred).

Fixpoint predn n := match n with 0 => 0 | S n => S (predn n) end.

Elpi param predn prednR.

Check (prednR : nat2natR predn predn).
Check (plusR : nat2nat2natR plus plus).

Fixpoint quasidn n m := S (match n with 0 => m | S n => S (quasidn n m) end).
Elpi Query param "param-const {{@quasidn}} _ _ _ _ XR _".

Fixpoint weirdn n := match n with S (S n) => S (weirdn n) | _ => 0 end.
Elpi Query param "param-const {{@weirdn}} _ _ _ _ XR _".

Inductive bla : nat -> Type := Bla : nat -> bla 0 | Blu n : bla n -> bla 1.
Elpi param bla blaR.

Elpi Query param "coq-TC-db-for {term->gr {{@param_db}}} PDb".

Fixpoint silly (n : nat) := n.
Elpi param silly sillyR.


