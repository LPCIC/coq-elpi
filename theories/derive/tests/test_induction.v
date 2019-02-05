From elpi Require Import derive.induction.

From elpi Require Import test_derive_stdlib test_param1 test_map.
Import test_derive_stdlib.Coverage.

Module Coverage.
Elpi derive.induction empty.
Elpi derive.induction unit.
Elpi derive.induction peano.
Elpi derive.induction option.
Elpi derive.induction pair.
Elpi derive.induction seq.
Elpi derive.induction rose.
Fail Elpi derive.induction nest.
Fail Elpi derive.induction w.
Elpi derive.induction vect.
Fail Elpi derive.induction dyn.
Fail Elpi derive.induction zeta.
Elpi derive.induction beta.
Elpi derive.induction iota.
Elpi derive.induction large.
End Coverage.

Import Coverage.
Import test_param1.Coverage.

Check empty_induction : forall P, forall x, is_empty x -> P x.
Check unit_induction : forall P, P tt -> forall x, is_unit x -> P x.
Check peano_induction : forall P, P Zero -> (forall n, P n -> P (Succ n)) -> forall x, is_peano x -> P x.
Check option_induction : forall A PA P, (P (None A)) -> (forall a, PA a -> P (Some A a)) -> forall x, is_option A PA x -> P x.
Check pair_induction : forall A PA B PB P, (forall a, PA a -> forall b, PB b -> P (Comma A B a b)) -> forall x, is_pair A PA B PB x -> P x.
Check seq_induction : forall A PA P, P (Nil A) -> (forall x, PA x -> forall xs, P xs -> P (Cons A x xs)) -> forall l, is_seq A PA l -> P l.
Check rose_induction : forall A PA P, (forall x, PA x -> P (Leaf A x)) -> (forall l, is_seq (rose A) P l -> P (Node A l)) -> forall x, is_rose A PA x -> P x.
Fail Check nest_induction.
Fail Check w_induction.
Check vect_induction : forall A PA (P : forall n, is_peano n -> vect A n -> Type), P Zero is_Zero (VNil A) -> (forall a, PA a -> forall n, forall nR: is_peano n, forall v : vect A n, P n nR v -> P (Succ n) (is_Succ n nR) (VCons A a n v)) -> forall l lR x, is_vect A PA l lR x -> P l lR x.
Fail Check dyn_induction.
Fail Check zeta_induction.
Check iota_induction.
Check large_induction.