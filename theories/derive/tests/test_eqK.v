From elpi Require Import elpi derive.eqK.

From elpi Require Import
  test_derive_stdlib
  test_isK
  test_projK
  test_bcongr
  tests.test_eq. (* conflict in attic *)

Import test_derive_stdlib.Coverage.
Import test_isK.Coverage.
Import test_projK.Coverage.
Import test_bcongr.Coverage.
Import tests.test_eq.Coverage.

Module Coverage.
Elpi derive.eqK empty.
Elpi derive.eqK unit.
Elpi derive.eqK peano.
Elpi derive.eqK option.
Elpi derive.eqK pair.
Elpi derive.eqK seq.
Elpi derive.eqK rose.
Fail Elpi derive.eqK nest.
Fail Elpi derive.eqK w.
Fail Elpi derive.eqK vect.
Fail Elpi derive.eqK dyn.
Elpi derive.eqK zeta.
Elpi derive.eqK beta.
Fail Elpi derive.eqK iota.
Elpi derive.eqK large.

End Coverage.

Import Coverage.
Import test_eq.Coverage.

Check eq_axiom_tt : eq_axiom unit unit_eq tt.

Check eq_axiom_Zero : eq_axiom peano peano_eq Zero.
Check eq_axiom_Succ : forall y, eq_axiom peano peano_eq y -> eq_axiom peano peano_eq (Succ y).

Check eq_axiom_None : forall A f, eq_axiom (option A) (option_eq A f) (None A).
Check eq_axiom_Some : forall A f x, eq_axiom A f x -> eq_axiom (option A) (option_eq A f) (Some A x).

Check eq_axiom_Comma: forall A f B g, forall x, eq_axiom A f x -> forall y, eq_axiom B g y -> eq_axiom (pair A B) (pair_eq A f B g) (Comma A B x y).

Check eq_axiom_Nil: forall A f, eq_axiom (seq A) (seq_eq A f) (Nil A).
Check eq_axiom_Cons : forall A f x, eq_axiom A f x -> forall xs, eq_axiom (seq A) (seq_eq A f) xs -> eq_axiom (seq A) (seq_eq A f) (Cons A x xs).

Check eq_axiom_Leaf: forall A f a, eq_axiom A f a -> eq_axiom (rose A) (rose_eq A f) (Leaf A a).
Check eq_axiom_Node: forall A f l, eq_axiom (seq (rose A)) (seq_eq (rose A) (rose_eq A f)) l -> eq_axiom (rose A) (rose_eq A f) (Node A l).

Check eq_axiom_Envelope.

Check eq_axiom_Redex.

Check eq_axiom_K1.