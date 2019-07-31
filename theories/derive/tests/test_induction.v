From elpi Require Import derive.induction.

From elpi Require Import test_derive_stdlib test_param1 test_param1_functor.

Import test_derive_stdlib.Coverage.
Import test_param1.Coverage.
Import test_param1_functor.Coverage.

Module Coverage.
Elpi derive.induction empty.
Elpi derive.induction unit.
Elpi derive.induction peano.
Elpi derive.induction option.
Elpi derive.induction pair.
Elpi derive.induction seq.
Elpi derive.induction rose.
Elpi derive.induction nest.
Elpi derive.induction w.
Elpi derive.induction vect.
Elpi derive.induction dyn.
Elpi derive.induction zeta.
Elpi derive.induction beta.
Elpi derive.induction iota.
Elpi derive.induction large.
End Coverage.

Import Coverage.
Locate is_unit.

Check empty_induction : forall P, forall x, is_empty x -> P x.
Check unit_induction : forall P, P tt -> forall x, is_unit x -> P x.
Check peano_induction : forall P, P Zero -> (forall n, P n -> P (Succ n)) -> forall x, is_peano x -> P x.
Check option_induction : forall A PA P, (P (None A)) -> (forall a, PA a -> P (Some A a)) -> forall x, is_option A PA x -> P x.
Check pair_induction : forall A PA B PB P, (forall a, PA a -> forall b, PB b -> P (Comma A B a b)) -> forall x, is_pair A PA B PB x -> P x.
Check seq_induction : forall A PA P, P (Nil A) -> (forall x, PA x -> forall xs, P xs -> P (Cons A x xs)) -> forall l, is_seq A PA l -> P l.
Check rose_induction : forall A PA P, (forall x, PA x -> P (Leaf A x)) -> (forall l, is_seq (rose A) P l -> P (Node A l)) -> forall x, is_rose A PA x -> P x.
Check nest_induction : forall P : forall A : Type, (A -> Type) -> nest A -> Type, (forall A PA, P A PA (NilN A)) -> (forall A PA x, PA x -> forall xs, P (pair A A) (is_pair A PA A PA) xs -> P A PA (ConsN A x xs)) -> forall A PA n, is_nest A PA n -> P A PA n.
Check w_induction : forall A PA P, (forall f, (forall a, PA a -> P (f a)) -> P (via A f)) -> forall x, is_w A PA x -> P x.
Check vect_induction : forall A PA (P : forall n, is_peano n -> vect A n -> Type), P Zero is_Zero (VNil A) -> (forall a, PA a -> forall n, forall nR: is_peano n, forall v : vect A n, P n nR v -> P (Succ n) (is_Succ n nR) (VCons A a n v)) -> forall l lR x, is_vect A PA l lR x -> P l lR x.
Check dyn_induction : forall P, (forall T PT (t : T), PT t -> P (box T t)) -> forall x, is_dyn x -> P x.
Check zeta_induction : forall A PA P, (forall a, PA a -> forall c, PA c -> P (Envelope A a c)) -> forall x, is_zeta A PA x -> P x.
Check iota_induction.
Check large_induction.