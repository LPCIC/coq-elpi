From elpi Require Import derive.param1.

From elpi.derive Require Import
  test_derive_stdlib.

Module Coverage.

Elpi derive.param1 Coverage.empty.
Elpi derive.param1 Coverage.unit.
Elpi derive.param1 Coverage.peano.
Elpi derive.param1 Coverage.option.
Elpi derive.param1 Coverage.pair.
Elpi derive.param1 Coverage.seq.
Elpi derive.param1 Coverage.tree.
Elpi derive.param1 Coverage.nest.
Elpi derive.param1 Coverage.w.
Elpi derive.param1 Coverage.vect.
Elpi derive.param1 Coverage.dyn.
Fail Elpi derive.param1 Coverage.zeta.
Elpi derive.param1 Coverage.beta.
Elpi derive.param1 Coverage.iota.
Elpi derive.param1 Coverage.large.

End Coverage.



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
Elpi derive.param1 listR.
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

Elpi Query derive.param1 "reali {{O}} Y".
Elpi Query derive.param1 "reali {{S (S 0)}} Y".

Definition nat2nat := nat -> nat.
Definition nat2nat2nat := nat -> nat -> nat.
Elpi derive.param1 nat2nat.
Elpi derive.param1 nat2nat2nat.
Elpi derive.param1 pred.

Print predR.
Check (predR : nat2natR pred).

Fixpoint predn n := match n with 0 => 0 | S n => S (predn n) end.

Elpi derive.param1 predn.

Check (prednR : nat2natR predn).
Check (addR : nat2nat2natR plus).

Fixpoint quasidn n m := S (match n with 0 => m | S n => S (quasidn n m) end).
Elpi derive.param1 quasidn. 

Fixpoint weirdn n := match n with S (S n) => S (weirdn n) | _ => 0 end.
Elpi derive.param1 weirdn.

Inductive bla : nat -> Type := Bla : nat -> bla 0 | Blu n : bla n -> bla 1.
Elpi derive.param1 bla. Print blaR.

Elpi Query derive.param1 "coq.TC.db-for {term->gr {{@reali_db}}} PDb".

Fixpoint silly (n : nat) := n.
Elpi derive.param1 silly.
