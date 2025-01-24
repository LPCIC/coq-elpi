From elpi.apps Require Import derive.param2.

Set Uniform Inductive Parameters.

Elpi derive.param2 unit.
Elpi derive.param2 nat.
Elpi derive.param2 list.

(* The Parametricty plugin of K & L asks for an interactive proof here
   (the proof to be produced is the match over n in the nil branch) *)
Definition nth T (x0 : T) :=
  fix rec (n : nat) (l : list T) {struct n} : T :=
    match l, n with
    | nil, _ => x0
    | cons x _, 0 => x
    | cons _ xs, S m => rec m xs
    end.
Elpi derive.param2 nth.
Print nth_R.

Inductive fin : nat -> Type :=
    FO : fin 0 | FS : forall n : nat, fin n -> fin (S n).
Elpi derive.param2 fin.

Fixpoint fin_length  n (v : fin n) :=
  match v with FO => 0 | FS _ w => S (fin_length _ w) end.
Elpi derive.param2 fin_length.

Inductive vec (A : Type) : nat -> Type :=
    vnil : vec 0 | vcons : A -> forall n : nat, vec n -> vec (S n).
Elpi derive.param2 vec.

Fixpoint vec_length (A : Type) n (v : vec A n) :=
  match v with vnil _ => 0 | vcons _ _ _ w => S (vec_length _ _ w) end.
Elpi derive.param2 vec_length.
Elpi derive.param2 eq.
Elpi derive.param2 list_R.

Fixpoint plus' m n := match n with 0 => m | S n => S (plus' m n) end.
Elpi derive.param2 plus'.
Elpi derive.param2 plus.
Elpi derive.param2 prod.
Elpi derive.param2 fst.
Elpi derive.param2 snd.
Elpi derive.param2 Nat.divmod.
Elpi derive.param2 Nat.div.

Definition test m n p q r := m + n + p + q + r.
Elpi derive.param2 test.

Definition vec_length_type := forall (A : Type) (n : nat), vec A n -> nat.

Elpi derive.param2 vec_length_type.

Definition vec_length_rec (vec_length : vec_length_type)
  (A : Type) n (v : vec A n) :=
  match v with vnil _ => 0 | vcons _ _ _ w => S (vec_length _ _ w) end.
Elpi derive.param2 vec_length_rec.

Definition nat2nat := nat -> nat.
Definition nat2nat2nat := nat -> nat -> nat.
Elpi derive.param2 nat2nat.
Elpi derive.param2 nat2nat2nat.
Elpi derive.param2 pred.

Print pred_R.
Redirect "tmp" Check (pred_R : nat2nat_R pred pred).

Fixpoint predn n := match n with 0 => 0 | S n => S (predn n) end.

Elpi derive.param2 predn.

Redirect "tmp" Check (predn_R : nat2nat_R predn predn).
Redirect "tmp" Check (add_R : nat2nat2nat_R plus plus).

Fixpoint quasidn n m := S (match n with 0 => m | S n => S (quasidn n m) end).
Elpi derive.param2 quasidn.

Fixpoint weirdn n := match n with S (S n) => S (weirdn n) | _ => 0 end.
Elpi derive.param2 weirdn.

Inductive bla : nat -> Type := Bla : nat -> bla 0 | Blu n : bla n -> bla 1.
Elpi derive.param2 bla.

Fixpoint silly (n : nat) := n.
Elpi derive.param2 silly.

Definition size_of (A : Type) := A -> nat.

Definition size_seq (A : Type) : size_of (list A) := fun _ => 0.

Elpi derive.param2 size_of.

Elpi derive.param2 size_seq.  (* Fixed by https://github.com/LPCIC/coq-elpi/pull/754 *)
