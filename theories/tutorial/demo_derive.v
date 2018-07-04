From elpi Require Import derive.

(* Some commands shipped with coq-elpi *)

Elpi derive nat.
Print Module nat.
Print Module nat.eq.
Print axiom.

Elpi derive list.
Print Module list.
Check list.eq.correct.
Check list.induction.
Check list.induction.principle.

Inductive tree := Leaf | Node : list tree -> tree.

About tree_ind.

Elpi derive tree.
Check tree.induction.principle.
Check tree.eq.OK.
Print tree.eq.correct.
