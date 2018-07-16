From elpi Require Import derive.

(* Some commands shipped with coq-elpi *)

Elpi derive nat.
Print Module nat.
Check nat.eq.OK.
Print axiom.
Print nat.param1.nat.

Elpi derive list.
Print Module list.
Check list.induction.
Print list.param1.list.
Check list.induction.principle.

Inductive tree := Leaf | Node : list tree -> tree.

About tree_ind.

Elpi derive tree.
Check tree.induction.principle.
Check tree.induction.
Check tree.eq.OK.
Print tree.eq.OK.
Print tree.eq.correct.
