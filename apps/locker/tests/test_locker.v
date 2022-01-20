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
