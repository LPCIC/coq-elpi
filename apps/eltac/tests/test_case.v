From elpi.apps Require Import eltac.case.

Lemma test1 (n : nat) : n = n.
Proof.
eltac.case n.
  exact (refl_equal 0).
exact (refl_equal (S _)).
Qed.

Inductive is_even : nat -> Prop :=
| even0 : is_even 0
| evenS : forall x, is_even x -> is_even (S (S x)).

Lemma test2 (n : nat) (H : is_even n) : n = n.
Proof.
eltac.case H.
  exact (refl_equal 0).
exact (refl_equal (S (S _))).
Qed.

Axiom q : nat -> Prop.
Axiom p0 : q 0.

(* The last 0 must not be abstracted or the goal is illtyped *)
Lemma test3 (H : is_even 0) : 0 = 0 /\ (@eq (q 0) p0 p0).
Proof.
eltac.case H.
  split. exact (refl_equal 0). exact (refl_equal p0).
split; [ exact (refl_equal (S (S _))) | exact (refl_equal p0) ].
Qed.
