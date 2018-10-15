From elpi Require Import test_derive_stdlib derive.isK.

(* coverage *)
Module Coverage.
Elpi derive.isK Coverage.empty.
Elpi derive.isK Coverage.unit.
Elpi derive.isK Coverage.peano.
Elpi derive.isK Coverage.option.
Elpi derive.isK Coverage.pair.
Elpi derive.isK Coverage.seq.
Elpi derive.isK Coverage.tree.
Elpi derive.isK Coverage.nest.
Elpi derive.isK Coverage.w.
Elpi derive.isK Coverage.vect.
Elpi derive.isK Coverage.dyn.
Fail Elpi derive.isK Coverage.zeta.
Elpi derive.isK Coverage.beta.
Elpi derive.isK Coverage.iota.
Elpi derive.isK Coverage.large.
End Coverage.

(* functional correctness *)

Set Implicit Arguments.

Inductive foo (A B : Type) : nat -> Type :=
 | K : foo A B 0
 | K1 : forall n, foo A B n -> foo A B (S n)
 | K2 : forall n, (A -> foo A (B*B) n) -> foo A B (n+n).

Elpi derive.isK foo.


Section ctx.

Variables A B : Type.
Variable n : nat.
Variable x : foo A B n.
Variable f : A -> foo A (B*B) n.

Example test_isK : foo_is_K (K A B) = true /\ foo_is_K (K1 x) = false /\ foo_is_K (K2 f) = false.
Proof. repeat split. Qed.

Example test_isK1 : foo_is_K1 (K A B) = false /\ foo_is_K1 (K1 x) = true /\ foo_is_K1 (K2 f) = false.
Proof. repeat split. Qed.

Example test_isK2 : foo_is_K2 (K A B) = false /\ foo_is_K2 (K1 x) = false /\ foo_is_K2 (K2 f) = true.
Proof. repeat split. Qed.

End ctx.
