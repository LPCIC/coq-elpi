From elpi.apps Require Import derive derive.param2.
From elpi.apps.derive.tests Require Import test_derive_corelib.

Set Uniform Inductive Parameters.

Elpi derive.param2 unit.
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

Definition fa := 0.
Definition fb := fa.

Fail Elpi derive.param2 fb.

Definition fa_R := O_R.
Elpi derive.param2.register fa fa_R.
Elpi derive.param2 fb.

Inductive Acc {A : Type} (R : A -> A -> Prop) | (x : A) : Prop :=
    Acc_intro : (forall y : A, R y x -> Acc y) -> Acc x.
Elpi derive.param2 Acc.

Definition fi T := fix g (s : list T) := tt.

Elpi derive.param2 fi.

Set Universe Polymorphism.
Inductive Nat :=
| O'
| S' (n : Nat).
Elpi derive.param2 Nat.

Definition Wrap := nat.
Definition WrapR := nat_R.
Elpi derive.param2.register "Wrap" "WrapR".

Definition Wrap2Wrap := Wrap -> Wrap.
Elpi derive.param2 Wrap2Wrap.

Unset Universe Polymorphism.

Inductive RenamedParam (n : nat) := renamedParam (_ : unit).
Arguments renamedParam m t : rename.
Elpi derive.param2 RenamedParam.

Record Box (A : Type) :=
  mkBox {
      unbox : A
    }.
Elpi derive.param2 Box.
Elpi derive.param2 unbox.

Definition box := mkBox.
Elpi derive.param2 box.

Set Primitive Projections.
Record BoxP (A : Type) :=
  mkBoxP {
      unboxP : A
    }.
Elpi derive.param2 BoxP.
Fail Elpi derive.param2 unboxP.

Definition boxP := mkBoxP.
Elpi derive.param2 boxP.

Unset Primitive Projections.

Module MutualCoreTests.

Import test_derive_corelib.Coverage.
Import test_derive_corelib.Mutual.Dependency.

Elpi derive.param2 mempty.
Redirect "tmp" Check mempty_R : mempty -> mempty -> Type.
Redirect "tmp" Check mempty'_R : mempty' -> mempty' -> Type.

Elpi derive.param2 munit.
Redirect "tmp" Check munit_R : munit -> munit -> Type.
Redirect "tmp" Check munit'_R : munit' -> munit' -> Type.

Elpi derive.param2 mpeano.
Redirect "tmp" Check mpeano_R : mpeano -> mpeano -> Type.
Redirect "tmp" Check mpeano'_R : mpeano' -> mpeano' -> Type.

Elpi derive.param2 moption.
Redirect "tmp" Check moption_R : forall A A1, (A -> A1 -> Type) -> moption A -> moption A1 -> Type.
Redirect "tmp" Check moption'_R : forall A A1, (A -> A1 -> Type) -> moption' A -> moption' A1 -> Type.

Elpi derive.param2 mtree.
Redirect "tmp" Check mtree_R : forall A A1, (A -> A1 -> Type) -> mtree A -> mtree A1 -> Type.
Redirect "tmp" Check mforest_R : forall A A1, (A -> A1 -> Type) -> mforest A -> mforest A1 -> Type.

Elpi derive.param2 a.
Elpi derive.param2 c.
Redirect "tmp" Check c_R : c -> c -> Type.

End MutualCoreTests.

Module MutualCoreNonFirst.
  From elpi.apps Require Import derive.param2.

  Import test_derive_corelib.Mutual.Tree.

  Elpi derive.param2 forest.

  Redirect "tmp" Check tree_R : tree -> tree -> Type.
  Redirect "tmp" Check forest_R : forest -> forest -> Type.
  Redirect "tmp" Check node_R.
  Redirect "tmp" Check empty_R.
  Redirect "tmp" Check cons_R.
  Redirect "tmp" Elpi Query derive.param2 lp:{{
    param.gref {{:gref tree}} {{:gref tree}} _,
    param.gref {{:gref forest}} {{:gref forest}} _
  }}.
End MutualCoreNonFirst.

Module MutualMetaFirst.
  From elpi.apps Require Import derive.param2.

  Import test_derive_corelib.Mutual.Tree.

  #[only(param2)] derive tree.

  Redirect "tmp" Check tree_R : tree -> tree -> Type.
  Redirect "tmp" Check forest_R : forest -> forest -> Type.
  Redirect "tmp" Elpi Query derive.param2 lp:{{
    param.gref {{:gref tree}} {{:gref tree}} _,
    param.gref {{:gref forest}} {{:gref forest}} _
  }}.
End MutualMetaFirst.

Module MutualMetaSecond.
  From elpi.apps Require Import derive.param2.

  Import test_derive_corelib.Mutual.Tree.

  #[only(param2)] derive forest.

  Redirect "tmp" Check tree_R : tree -> tree -> Type.
  Redirect "tmp" Check forest_R : forest -> forest -> Type.
  Redirect "tmp" Elpi Query derive.param2 lp:{{
    param.gref {{:gref tree}} {{:gref tree}} _,
    param.gref {{:gref forest}} {{:gref forest}} _
  }}.
End MutualMetaSecond.
