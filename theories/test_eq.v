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
Elpi Run "create-eq-from-name ""mlist"".".
Check mlist_equal.
Elpi Run "create-eq-from-name ""prod"".".
Check prod_equal.

Elpi Run "create-eq-from-name ""nat"".".
Elpi Accumulate "
  eq-function {{nat}} {{nat_equal}}.
".

Elpi Run "create-eq-from-name ""mbtree"".".
Elpi Accumulate "
  eq-function {{mbtree}} {{mbtree_equal}}.
".

Check mbtree_equal.

Definition eq_pairnat (a b : nat * nat) : bool :=
match (a,b) with
| ((x1,y1),(x2,y2)) => andb (eq_nat x1 x2) (eq_nat y1 y2)
end.

Compute (mbtree_equal eq_pairnat
  (mbnode (mbleaf (1,2))
          (mbnode (mbleaf (3,4)) (mbleaf (5,6)) 7)
          8
  )
  (mbnode (mbleaf (1,2))
          (mbnode (mbleaf (4,4)) (mbleaf (5,6)) 7)
          8
  )
).




