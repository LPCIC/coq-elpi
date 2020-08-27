From elpi.apps Require Import derive.param1_trivial.

From elpi.apps Require Import test_derive_stdlib test_param1 test_param1_inhab test_param1_congr.
Import test_derive_stdlib.Coverage.
Import test_param1.Coverage.
Import test_param1_inhab.Coverage.
Import test_param1_congr.Coverage.

Module Coverage.

Elpi derive.param1.trivial is_empty.
Elpi derive.param1.trivial is_unit.
Elpi derive.param1.trivial is_peano.
Elpi derive.param1.trivial is_option.
Elpi derive.param1.trivial is_pair.
Elpi derive.param1.trivial is_seq.
Fail Elpi derive.param1.trivial is_nest.
Elpi derive.param1.trivial is_rose.
Fail Elpi derive.param1.trivial is_w.
Fail Elpi derive.param1.trivial is_vect.
Fail Elpi derive.param1.trivial is_dyn.
Elpi derive.param1.trivial is_zeta.
Elpi derive.param1.trivial is_beta.
Fail Elpi derive.param1.trivial is_iota.
Fail Elpi derive.param1.trivial is_large.
Elpi derive.param1.trivial is_prim_int.
Elpi derive.param1.trivial is_prim_float.

End Coverage.

Import Coverage.

Check is_empty_trivial : trivial empty is_empty.
Check is_unit_trivial : trivial unit is_unit.
Check is_peano_trivial : trivial peano is_peano.
Check is_option_trivial : forall A P, trivial A P -> trivial (option A) (is_option A P).
Check is_pair_trivial : forall A P, trivial A P -> forall B Q, trivial B Q -> trivial (pair A B) (is_pair A P B Q).
Check is_seq_trivial : forall A P, trivial A P -> trivial (seq A) (is_seq A P).
Check is_rose_trivial : forall A P, trivial A P -> trivial (rose A) (is_rose A P).
Fail Check is_nest_trivial.
Fail Check is_w_trivial : forall A P, trivial A P -> trivial (w A) (is_w A P).
Fail Check is_vect_trivial : forall A P, trivial A P -> forall i pi, trivial (vect A i) (is_vect A P i pi).
Fail Check is_dyn_trivial.
Check is_zeta_trivial : forall A P, trivial A P -> trivial (zeta A) (is_zeta A P).
Check is_beta_trivial : forall A P, trivial A P -> trivial (beta A) (is_beta A P).
Fail Check is_iota_trivial.
Fail Check is_large_trivial : trivial large is_large.
Check is_prim_int_trivial : trivial prim_int is_prim_int.
Check is_prim_float_trivial : trivial prim_float is_prim_float.
