From elpi Require Import derive.

Inductive rtree A := Leaf (a : A) | Node (l : list (rtree A)).
About rtree_ind.

Unset Elimination Schemes.

Elpi derive nat.

About nat_eq_OK.

Elpi derive list.

About list_induction.
About list_eq_correct.

Elpi derive rtree.

About rtree_induction.
Print rtree_eq.
About rtree_eq_correct.
Print rtree_eq_correct.
