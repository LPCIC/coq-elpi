From elpi.apps Require Import derive.param2.

Elpi derive.param2 unit R.
Elpi derive.param2 nat R.
Elpi derive.param2 list R.

(* The Parametricty plugin of K & L asks for an interactive proof here
   (the proof to be produced is the match over n in the nil branch) *)
Definition nth T (x0 : T) :=
  fix rec (n : nat) (l : list T) {struct n} : T :=
    match l, n with
    | nil, _ => x0
    | cons x _, 0 => x
    | cons _ xs, S m => rec m xs
    end.
Elpi derive.param2 nth R.
Print nthR.

Inductive fin : nat -> Type :=
    FO : fin 0 | FS : forall n : nat, fin n -> fin (S n).
Elpi derive.param2 fin R.

Fixpoint fin_length  n (v : fin n) :=
  match v with FO => 0 | FS _ w => S (fin_length _ w) end.
Elpi derive.param2 fin_length R.

Inductive vec (A : Type) : nat -> Type :=
    vnil : vec A 0 | vcons : A -> forall n : nat, vec A n -> vec A (S n).
Elpi derive.param2 vec R.

Fixpoint vec_length (A : Type) n (v : vec A n) :=
  match v with vnil _ => 0 | vcons _ _ _ w => S (vec_length _ _ w) end.
Elpi derive.param2 vec_length R.
Elpi derive.param2 eq R.
Elpi derive.param2 listR R.

Fixpoint plus' m n := match n with 0 => m | S n => S (plus' m n) end.
Elpi derive.param2 plus' R.
Elpi derive.param2 plus R.
Elpi derive.param2 prod R.
Elpi derive.param2 fst R.
Elpi derive.param2 snd R.
Elpi derive.param2 Nat.divmod R.
Elpi derive.param2 Nat.div R.

Definition test m n p q r := m + n + p + q + r.
Elpi derive.param2 test R.

Definition vec_length_type := forall (A : Type) (n : nat), vec A n -> nat.

Elpi derive.param2 vec_length_type R.

Definition vec_length_rec (vec_length : vec_length_type)
  (A : Type) n (v : vec A n) :=
  match v with vnil _ => 0 | vcons _ _ _ w => S (vec_length _ _ w) end.
Elpi derive.param2 vec_length_rec R.

Definition nat2nat := nat -> nat.
Definition nat2nat2nat := nat -> nat -> nat.
Elpi derive.param2 nat2nat R.
Elpi derive.param2 nat2nat2nat R.
Elpi derive.param2 pred R.

Print predR.
Check (predR : nat2natR pred pred).

Fixpoint predn n := match n with 0 => 0 | S n => S (predn n) end.

Elpi derive.param2 predn R.

Check (prednR : nat2natR predn predn).
Check (addR : nat2nat2natR plus plus).

Fixpoint quasidn n m := S (match n with 0 => m | S n => S (quasidn n m) end).
Elpi derive.param2 quasidn R.

Fixpoint weirdn n := match n with S (S n) => S (weirdn n) | _ => 0 end.
Elpi derive.param2 weirdn R.

Inductive bla : nat -> Type := Bla : nat -> bla 0 | Blu n : bla n -> bla 1.
Elpi derive.param2 bla R.

Fixpoint silly (n : nat) := n.
Elpi derive.param2 silly R.

