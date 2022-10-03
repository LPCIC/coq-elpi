From elpi.apps Require Import derive.induction.

From elpi.apps Require Import test_derive_stdlib test_param1 test_param1_functor.

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
Elpi derive.induction box_peano.
Elpi derive.induction rose.
Elpi derive.induction rose_p.
Elpi derive.induction rose_o.
Elpi derive.induction nest.
Elpi derive.induction w.
Elpi derive.induction vect.
Elpi derive.induction dyn.
Elpi derive.induction zeta.
Elpi derive.induction beta.
Elpi derive.induction iota.
Elpi derive.induction large.
Elpi derive.induction prim_int.
Elpi derive.induction prim_float.
Elpi derive.induction fo_record.
Elpi derive.induction pa_record.
Elpi derive.induction pr_record.
Elpi derive.induction dep_record.
Elpi derive.induction enum.
Elpi derive.induction eq.
Elpi derive.induction bool.
Elpi derive.induction sigma_bool.
Elpi derive.induction ord.
Elpi derive.induction ord2.
Elpi derive.induction val.
End Coverage.

Import Coverage.
Locate is_unit.

Check empty_induction : forall P : empty -> Prop, forall x, is_empty x -> P x.
Check unit_induction : forall P : unit -> Prop, P tt -> forall x, is_unit x -> P x.
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
Check prim_int_induction.
Check prim_float_induction.
Check fo_record_induction : forall P, (forall x, is_peano x -> forall y, is_unit y -> P (Build_fo_record x y)) -> forall x, is_fo_record x -> P x.
Check pa_record_induction : forall A PA P, (forall x, is_peano x -> forall y, PA y -> P (Build_pa_record A x y)) -> forall x, is_pa_record A PA x -> P x.
Check pr_record_induction : forall A pr P, (forall x, is_peano x -> forall y, pr y -> P (Build_pr_record A x y)) -> forall x, is_pr_record A pr x -> P x.
Check dep_record_induction : forall P, (forall x (px : is_peano x) y, is_vect unit is_unit x px y -> P (Build_dep_record x y)) -> forall x, is_dep_record x -> P x.
Check enum_induction : forall P, (P E1) -> (P E2) -> (P E3) -> forall x, is_enum x -> P x.
Check sigma_bool_induction.
Check ord_induction : forall p Pp P, (forall n Pn l, is_eq bool is_bool (is_leq n p) (is_is_leq n Pn p Pp) true is_true l -> P (mkOrd p n l)) -> forall (o : ord p), is_ord p Pp o -> P o.
Check ord2_induction : forall p Pp P, (forall (o1 : ord p), is_ord p Pp o1 -> forall (o2 : ord p), is_ord p Pp o2 -> P (mkOrd2 p o1 o2)) -> forall (o : ord2 p), is_ord2 p Pp o -> P o.
