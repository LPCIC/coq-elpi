From elpi.apps Require Import derive.param1 derive.invert derive.induction derive.idx2inv.

Elpi derive.param1 list.
Elpi derive.invert is_list.
Elpi derive.idx2inv is_list.

Check is_list_to_is_list_inv :
  forall A PA l, is_list A PA l -> is_list_inv A PA l.