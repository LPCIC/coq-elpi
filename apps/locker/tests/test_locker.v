From Coq Require Import ssreflect.
From elpi.apps Require Import locker.

(* ----------------------- *)

lock Definition d1 := 3.

Lemma test_1_0 : d1 = 3.
Proof. rewrite unlock. match goal with |- 3 = 3 => by [] end. Qed.
Lemma test_1_1 : d1 = 3.
Proof. unfold d1. match goal with |- locked_with d1_key_subproof 3 = 3 => by rewrite unlock end. Qed.

(* ----------------------- *)

Fail lock Axiom d2 : nat.

(* ----------------------- *)

Section S1.
Variable T : Type.
#[key="foo"] lock Definition d2 (x : T) := x.
End S1.

Lemma test_2_0 : d2 nat 3 = 3.
Proof. unfold d2. match goal with |- locked_with foo (fun x => x) 3 = 3 => by rewrite unlock end. Qed.


(* ----------------------- *)

mlock Definition d3 := 3.

Print Module d3.
Print Module Type d3_Locked.
Lemma test_3_0 : d3 = 3.
Proof. rewrite unlock. match goal with |- 3 = 3 => by [] end. Qed.
Lemma test_3_1 : d3 = 3.
Proof. Fail unfold d3. rewrite d3.unlock. by []. Qed.

Module test_global_implicits.
  Module mlock_container.
    mlock Definition def {A} (a : A) := a.
  End mlock_container.

  Fail Definition user1 {A} (a : A) := mlock_container.def _ a.
  Definition user1 {A} (a : A) := mlock_container.def a.

  Import mlock_container.
  Fail Definition user2 {A} (a : A) := def _ a.
  Definition user2 {A} (a : A) := def a.
End test_global_implicits.

(* ----------------------- *)

Section S2.
Fail mlock Definition d4 := 3.
End S2.

(* #286 ----------------------- *)

Module Bug_286.
Unset Implicit Arguments.
lock Definition cons2 {A} x xs := @cons A x xs.
About cons2.
Definition foo := cons2 0 nil.
Class EqDecision (A : Type) := { f : A -> A -> bool }.
#[local] Instance xx : EqDecision nat := {| f := (fun _ _ => true) |}.
lock Definition cons3 [A] `{EqDecision A} x xs := @cons A x xs.
Definition foo3 := cons3 0 nil.
About cons3.
End Bug_286.

(* https://coq.zulipchat.com/#narrow/stream/253928-Elpi-users-.26-devs/topic/Reifying.20terms.20with.20ltac.20.2F.20if-then-else.20.2F.20complex.20match *)

Module elab.
mlock Definition y (z : nat) := ltac:(exact z).
mlock Definition q (b : bool) := if b then 1 else 0.
End elab.

(* ----------------------- *)

Elpi Command test. (* for queries *)

Set Printing Universes.

lock #[universes(polymorphic)] Definition id1@{u} (T : Type@{u}) (x : T) := x.
About id1.
Elpi Query lp:{{ coq.locate "id1" GR, coq.env.univpoly? GR 1 }}.


mlock #[universes(polymorphic)] Definition id2@{u} (T : Type@{u}) (x : T) := x.
About id2.body.
Elpi Query lp:{{ coq.locate "id2" GR, coq.env.univpoly? GR 1 }}.

Set Universe Polymorphism.

mlock Definition up1 (T : Type) (x : T) := x.
About up1.body.
Elpi Query lp:{{ coq.locate "up1" GR, coq.env.univpoly? GR 1 }}.

mlock #[universes(polymorphic=no)] Definition nup1 (T : Type) (x : T) := x.
About nup1.body.
Elpi Query lp:{{ coq.locate "nup1" GR, not(coq.env.univpoly? GR _) }}.

mlock Definition up2@{u +} (T : Type@{u}) (W : Type) (x : T) := x.
About up2.body.
Elpi Query lp:{{ coq.locate "up2" GR, coq.env.univpoly? GR 2 }}.

Fail mlock Definition up3@{u} (T : Type@{u}) (W : Type) (x : T) := x.
