From elpi Require Import test_derive_stdlib derive.eq.

Module Coverage.
Elpi derive.eq Coverage.empty.
Elpi derive.eq Coverage.unit.
Elpi derive.eq Coverage.peano.
Elpi derive.eq Coverage.option.
Elpi derive.eq Coverage.pair.
Elpi derive.eq Coverage.seq.
Elpi derive.eq Coverage.tree.
Fail Elpi derive.eq Coverage.nest.
Fail Elpi derive.eq Coverage.w.
Elpi derive.eq Coverage.vect.
Fail Elpi derive.eq Coverage.dyn.
Fail Elpi derive.eq Coverage.zeta.
Fail Elpi derive.eq Coverage.beta.
Fail Elpi derive.eq Coverage.iota.
Elpi derive.eq Coverage.large.
End Coverage.



From Coq Require Vector.

Set Implicit Arguments.

Elpi derive.eq nat.
Elpi derive.eq list.
Inductive Foo A := K1 (_ : list nat) | K2 (n : list A) (l : list (Foo A)).
Elpi derive.eq Foo.

Elpi derive.eq Vector.t.

Check t_eq : forall A (f : A -> A -> bool) i (v1 v2 : Vector.t A i), bool.
