From elpi Require Import elpi.

Elpi Init "./" "./elpi/".

Elpi Accumulate File "pervasives.elpi".
Elpi Accumulate File "coq-lib.elpi".

Inductive mbtree :=
| mbnode : mbtree -> mbtree -> nat -> mbtree
| mbleaf : nat * nat -> mbtree.

Fixpoint eq_nat (n m : nat) :=
  match n with
  | O   => match m with
           | O   => true
           | S _ => false
           end
  | S x => match m with
           | O   => false
           | S y => eq_nat x y
           end
  end.

Definition tmp (f : nat -> nat -> bool)
(a b : mbtree) := true.

Elpi Accumulate File "eq.elpi".

Elpi Run "test-prod.".
Elpi Run "test-list.".

Elpi Run "create-eq-from-name ""nat"".".
Elpi Accumulate "eq-test {{nat}} {{nat_equal}}
  {{nat -> nat -> bool}}.".

Elpi Run "create-eq-from-name ""mbtree"".".
Elpi Accumulate "eq-test {{mbtree}}
                         {{mbtree_equal}}
  {{((nat * nat) -> (nat * nat) -> bool)
    -> mbtree -> mbtree -> bool}}.".

Check mbtree_equal.

Inductive awful A :=
| mkawful : awful (list A) -> awful A
| awful_nil : A -> awful A.


