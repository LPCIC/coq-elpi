From elpi Require Import derive.bcongr.

From elpi Require Import test_derive_stdlib test_projK.

Import test_derive_stdlib.Coverage.
Import test_projK.Coverage.

Module Coverage.
Elpi derive.bcongr empty.
Elpi derive.bcongr unit.
Elpi derive.bcongr peano.
Elpi derive.bcongr option.
Elpi derive.bcongr pair.
Elpi derive.bcongr seq.
Elpi derive.bcongr rose.
Elpi derive.bcongr nest.
Elpi derive.bcongr w.
Fail Elpi derive.bcongr vect.
Fail Elpi derive.bcongr dyn.
Elpi derive.bcongr zeta.
Elpi derive.bcongr beta.
Fail Elpi derive.bcongr iota.
Elpi derive.bcongr large.
End Coverage.

Import Coverage.

Check unit_bcongr_tt : reflect (tt = tt) true.

Check peano_bcongr_Zero : reflect (Zero = Zero) true.
Check peano_bcongr_Succ : forall x y b, reflect (x = y) b -> reflect (Succ x = Succ y) b.

Check option_bcongr_None : forall A, reflect (None A = None A) true.
Check option_bcongr_Some : forall A x y b, reflect (x = y) b -> reflect (Some A x = Some A y) b.

Check pair_bcongr_Comma : forall A B x1 x2 b1, reflect (x1 = x2) b1 -> forall y1 y2 b2, reflect (y1 = y2) b2 -> reflect (Comma A B x1 y1 = Comma A B x2 y2) (b1 && b2).

Check seq_bcongr_Nil : forall A, reflect (Nil A = Nil A) true.
Check seq_bcongr_Cons : forall A x y b1, reflect (x = y) b1 -> forall xs ys b2, reflect (xs = ys) b2 -> reflect (Cons A x xs = Cons A y ys) (b1 && b2).

Check rose_bcongr_Leaf : forall A x y b, reflect (x = y) b -> reflect (Leaf A x = Leaf A y) b.
Check rose_bcongr_Node : forall A l1 l2 b, reflect (l1 = l2) b -> reflect (Node A l1 = Node A l2) b.

Check nest_bcongr_NilN : forall A, reflect (NilN A = NilN A) true.
Check nest_bcongr_ConsN : forall A x y b1, reflect (x = y) b1 -> forall xs ys b2, reflect (xs = ys) b2 -> reflect (ConsN A x xs = ConsN A y ys) (b1 && b2).

Check w_bcongr_via : forall A f g b, reflect (f = g) b -> reflect (via A f = via A g) b.

Fail Check vect_bcongr_VNil.
Fail Check vect_bcongr_VCons.

Fail Check dyn_bcongr_box.

Check zeta_bcongr_Envelope :
  forall A x1 x2 b1, reflect (x1 = x2) b1 ->
    forall y1 y2 b2, reflect (y1 = y2) b2 ->
    reflect (Envelope A x1 y1 = Envelope A x2 y2) (b1 && b2).

Check beta_bcongr_Redex : forall A x y b, reflect (x = y) b -> reflect (Redex A x = Redex A y) b.

Fail Check iota_bcongr_Why.

Check large_bcongr_K1.
