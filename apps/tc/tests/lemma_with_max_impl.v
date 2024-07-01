From elpi.apps Require Import tc.

Class A (n : nat).
Instance a : A 0 := {}.

Class B (n : nat).

Class C (n : nat).
Instance b x: C x := {}.

Lemma foo: forall (x n: nat) `{A x} `{C n}, True -> B n. Admitted.
Lemma bar: forall (n: nat) `{A n}, True -> B n. Admitted.

Goal exists n, B n.
Proof.
  eexists.
  (* Note: `{A x} and `{C n} are solved with x = 0, n remains a hole *)
  (* Moreover, True remains as active goal + a shelved goal remain for n *)
  refine (foo _ _ _).
  auto.
  Unshelve.
  constructor.
Qed.

Goal exists x, B x.
Proof.
  eexists.
  (* Note: `{A x} is solved with x = 0 *)
  refine (bar _ _).
  auto.
Qed.


Goal exists x, C x. 
Proof.
  eexists.
  apply _.
  Unshelve.
  constructor.
Qed.

Class Decision (P : Type).

Goal forall (A : Type) (P1: A -> Prop),
  exists (P : A -> A -> A -> Prop), forall z y , (forall x, Decision (P1 x)) 
    -> forall x, Decision (P z y x).
Proof.
  eexists; intros.
  apply _.
  Unshelve.
  auto.
Qed.

Elpi Tactic A.
Elpi Accumulate  lp:{{
  msolve L _ :- coq.ltac.fail _ "[TC] fail to solve" L.
}}.
Goal exists n, B n.
  eexists.
  Fail apply _.
Abort.


