From elpi Require Import elpi.
Elpi Init "./" "./elpi/".

Elpi Accumulate File "pervasives.elpi".
Elpi Accumulate File "coq-lib.elpi".

Require Import Coq.Lists.List.

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

Definition tmp' (f : list nat -> list nat -> bool)
(a b : mbtree) := true.

Fixpoint eq_list (A : Type)
(eq : A -> A -> bool) (l1 l2 : list A) :=
match (l1,l2) with
| (cons x1 t1, cons x2 t2) => andb (eq x1 x2)
                         (eq_list A eq t1 t2)
| (nil,nil) => true
| _ => false
end.

Inductive awful A B :=
| mkawful : awful (list B) B -> awful A B
| awful_nil : B -> awful A B.

Inductive mlist A B :=
| mcons : A -> B -> mlist A B -> mlist A B
| mnil  : mlist A B.

Elpi Accumulate File "eq.elpi".

Elpi Run "create-eq-from-name ""prod"".".
Elpi Accumulate "
  eq-function {{prod}} {{prod_equal}}.
".

Elpi Run "create-eq-from-name ""nat"".".
Elpi Accumulate "
  eq-function {{nat}} {{nat_equal}}.
".

Elpi Run "create-eq-from-name ""mbtree"".".
Elpi Accumulate "
  eq-function {{mbtree}} {{mbtree_equal}}.
".
Check mbtree_equal.
Compute (mbtree_equal
  (mbnode (mbleaf (1,2))
          (mbnode (mbleaf (3,4)) (mbleaf (5,6)) 7)
          8
  )
  (mbnode (mbleaf (1,2))
          (mbnode (mbleaf (4,4)) (mbleaf (5,6)) 7)
          8
  )
).

Elpi Run "create-eq-from-name ""mlist"".".
Check mlist_equal.
Elpi Accumulate "
  eq-function {{mlist}} {{mlist_equal}}.
".

Elpi Run "create-eq-from-name ""list"".".
Check list_equal.
Elpi Accumulate "
  eq-function {{list}} {{list_equal}}.
".
Check (list_equal nat nat_equal).
Compute (list_equal nat nat_equal
  (1::2::3::4::5::6::7::nil)
  (1::2::3::4::5::6::7::nil)
).
Compute (list_equal nat nat_equal
  (1::2::3::4::5::6::7::nil)
  (1::2::3::4::5::6::6::nil)
).

Elpi Run "create-eq-from-name ""awful"".".
Check awful_equal.
Elpi Accumulate "
  eq-function {{awful}} {{awful_equal}}.
".

Inductive FingerTree A :=
| ft_leaf : FingerTree A
| ft_node : A -> FingerTree A -> FingerTree (prod A A)
         -> FingerTree A.
Elpi Run "create-eq-from-name ""FingerTree"".".
Check FingerTree_equal.



