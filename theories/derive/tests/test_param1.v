From elpi Require Import derive.param1.

From elpi.derive Require Import test_derive_stdlib.
Import test_derive_stdlib.Coverage.

Module Coverage.

Elpi derive.param1 empty.
Elpi derive.param1 unit.
Elpi derive.param1 peano.
Elpi derive.param1 option.
Elpi derive.param1 pair.
Elpi derive.param1 seq.
Elpi derive.param1 rose.
Elpi derive.param1 nest.
Elpi derive.param1 w.
Elpi derive.param1 vect.
Elpi derive.param1 dyn.
Elpi derive.param1 zeta.
Elpi derive.param1 beta.
Elpi derive.param1 iota.
Elpi derive.param1 large.

End Coverage.

Import Coverage.

Section Test.
Local Notation pred X := (X -> Type).

Check is_empty : pred empty.
Check is_unit : pred unit.
Check is_peano : pred peano.
Check is_option : forall A, pred A -> pred (option A).
Check is_pair : forall A, pred A -> forall B, pred B -> pred (pair A B).
Check is_seq : forall A, pred A -> pred (seq A).
Check is_rose : forall A, pred A -> pred (rose A).
Check is_nest : forall A, pred A -> pred (nest A).
Check is_w : forall A, pred A -> pred (w A).
Check is_vect : forall A, pred A -> forall i, is_peano i -> pred (vect A i).
Check is_dyn : pred dyn.
Check is_zeta : forall A, pred A -> pred (zeta A).
Check is_beta : forall A, pred A -> pred (beta A).
Check is_iota : pred iota.
Check is_large : pred large.
End Test.

(* other tests by Cyril *)

Module OtherTests.

Elpi derive.param1 unit.
Elpi derive.param1 nat.

Inductive fin : nat -> Type :=
    FO : fin 0 | FS : forall n : nat, fin n -> fin (S n).
Elpi derive.param1 fin.
 
Fixpoint fin_length  n (v : fin n) :=
  match v with FO => 0 | FS _ w => S (fin_length _ w) end.

Elpi derive.param1 fin_length.

Inductive vec (A : Type) : nat -> Type :=
    vnil : vec A 0 | vcons : A -> forall n : nat, vec A n -> vec A (S n).
Elpi derive.param1 vec.

Fixpoint vec_length (A : Type) n (v : vec A n) :=
  match v with vnil _ => 0 | vcons _ _ _ w => S (vec_length _ _ w) end.
Elpi derive.param1 vec_length.
Elpi derive.param1 list.
Elpi derive.param1 is_list.
Elpi derive.param1 eq.

Fixpoint plus' m n := match n with 0 => m | S n => S (plus' m n) end.
Elpi derive.param1 plus'.
Elpi derive.param1 plus.
Elpi derive.param1 prod.
Elpi derive.param1 fst.
Elpi derive.param1 snd.
Elpi derive.param1 Nat.divmod.
Elpi derive.param1 Nat.div.

Definition test m n p q r := m + n + p + q + r.
Elpi derive.param1 test.

Definition vec_length_type := forall (A : Type) (n : nat), vec A n -> nat.

Elpi derive.param1 vec_length_type.

Definition vec_length_rec (vec_length : vec_length_type)
  (A : Type) n (v : vec A n) :=
  match v with vnil _ => 0 | vcons _ _ _ w => S (vec_length _ _ w) end.
Elpi derive.param1 vec_length_rec.

Elpi Query derive.param1 lp:{{ reali {{O}} Y }}.
Elpi Query derive.param1 lp:{{ reali {{S (S 0)}} Y }}.

Definition nat2nat := nat -> nat.
Definition nat2nat2nat := nat -> nat -> nat.
Elpi derive.param1 nat2nat.
Elpi derive.param1 nat2nat2nat.
Elpi derive.param1 pred.

Print is_pred.
Check (is_pred : is_nat2nat pred).

Fixpoint predn n := match n with 0 => 0 | S n => S (predn n) end.

Elpi derive.param1 predn.

Check (is_predn : is_nat2nat predn).
Check (is_add : is_nat2nat2nat plus).

Fixpoint quasidn n m := S (match n with 0 => m | S n => S (quasidn n m) end).
Elpi derive.param1 quasidn. 

Fixpoint weirdn n := match n with S (S n) => S (weirdn n) | _ => 0 end.
Elpi derive.param1 weirdn.

Inductive bla : nat -> Type := Bla : nat -> bla 0 | Blu n : bla n -> bla 1.
Elpi derive.param1 bla. Print is_bla.

Elpi Query derive.param1 lp:{{ coq.TC.db-for {term->gr {{@reali_db}}} PDb }}.

Fixpoint silly (n : nat) := n.
Elpi derive.param1 silly.

End OtherTests.