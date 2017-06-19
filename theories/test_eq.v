From elpi Require Import elpi.

Elpi Init "./" "./elpi/".

Elpi Accumulate File "pervasives.elpi".
Elpi Accumulate File "coq-lib.elpi".

Inductive mbtree :=
| mbnode : mbtree -> mbtree -> nat -> mbtree
| mbleaf : nat * nat -> mbtree.

Fixpoint eq_nat (n m : nat) :=
  match (n,m) with
  | (S x, S y) => eq_nat x y
  | (O, O)     => True
  | _          => False
  end.

Elpi Accumulate File "eq.elpi".

Elpi Run "create-eq-test".

Check mbtree_equal.

