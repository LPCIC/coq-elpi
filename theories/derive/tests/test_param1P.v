From elpi Require Import derive.param1P.

From elpi Require Import test_derive_stdlib test_param1.
Import test_derive_stdlib.Coverage.
Import test_param1.Coverage.

Module Coverage.

Elpi derive.param1P is_empty.
Elpi derive.param1P is_unit.
Elpi derive.param1P is_peano.
Elpi derive.param1P is_option.
Elpi derive.param1P is_pair.
Elpi derive.param1P is_seq.
Elpi derive.param1P is_rose.
Fail Elpi derive.param1P is_nest.
Fail Elpi derive.param1P is_w.
Fail Elpi derive.param1P is_vect.
Fail Elpi derive.param1P is_dyn.
Fail Elpi derive.param1P is_zeta.
Fail Elpi derive.param1P is_beta.
Fail Elpi derive.param1P is_iota.
Elpi derive.param1P is_large.

End Coverage.

Import Coverage.

Check empty_is_empty : forall x, is_empty x.
Check unit_is_unit : forall x, is_unit x.
Check peano_is_peano : forall x, is_peano x.
Check option_is_option : forall A P, (forall x : A, P x) -> forall l, is_option A P l.
Check pair_is_pair : forall A P, (forall x : A, P x) -> forall A1 P1, (forall x : A1, P1 x) -> forall l, is_pair A P A1 P1 l.
Check seq_is_seq : forall A P, (forall x : A, P x) -> forall l, is_seq A P l.
Check rose_is_rose : forall A P, (forall x : A, P x) -> forall l, is_rose A P l.
Fail Check nest_is_nest.
Fail Check w_is_w.
Fail Check vect_is_vect.
Fail Check dyn_is_dyn.
Fail Check zeta_is_zeta.
Fail Check beta_is_beta.
Fail Check iota_is_iota.
Check large_is_large.