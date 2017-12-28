From elpi Require Import derive.eq.
From Coq Require Vector.

Set Implicit Arguments.

Elpi derive.eq nat.
Elpi derive.eq list.
Inductive Foo A := K1 (_ : list nat) | K2 (n : list A) (l : list (Foo A)).
Elpi derive.eq Foo.

Elpi derive.eq Vector.t.

Check t_eq : forall A (f : A -> A -> bool) i (v1 v2 : Vector.t A i), bool.
