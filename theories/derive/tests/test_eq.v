From elpi Require Import derive.eq.

Set Implicit Arguments.

Elpi derive.eq nat.
Elpi derive.eq list.
Inductive Foo A := K1 (_ : list nat) | K2 (n : list A) (l : list (Foo A)).
Elpi derive.eq Foo.
