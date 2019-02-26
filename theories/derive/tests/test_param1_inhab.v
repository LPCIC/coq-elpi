From elpi Require Import derive.param1_inhab.

From elpi Require Import test_derive_stdlib test_param1.
Import test_derive_stdlib.Coverage.
Import test_param1.Coverage.


Module Coverage.

Elpi derive.param1.inhab is_empty.
Elpi derive.param1.inhab is_unit.
Elpi derive.param1.inhab is_peano.
Elpi derive.param1.inhab is_option.
Elpi derive.param1.inhab is_pair.
Elpi derive.param1.inhab is_seq.
Fail Elpi derive.param1.inhab is_nest.
Elpi derive.param1.inhab is_rose.
Elpi derive.param1.inhab is_w.
Fail Elpi derive.param1.inhab is_vect.
Fail Elpi derive.param1.inhab is_dyn.
Elpi derive.param1.inhab is_zeta.
Elpi derive.param1.inhab is_beta.
Fail Elpi derive.param1.inhab is_iota.
Elpi derive.param1.inhab is_large.

End Coverage.

Import Coverage.


Check is_empty_witness : full empty is_empty.
Check is_unit_witness : full unit is_unit.
Check is_peano_witness : full peano is_peano.
Check is_option_witness : forall A P, full A P -> full (option A) (is_option A P).
Check is_pair_witness : forall A P, full A P -> forall B Q, full B Q -> full (pair A B) (is_pair A P B Q).
Check is_seq_witness : forall A P, full A P -> full (seq A) (is_seq A P).
Check is_rose_witness : forall A P, full A P -> full (rose A) (is_rose A P).
Fail Check is_nest_witness.
Check is_w_witness : forall A P, full A P -> full (w A) (is_w A P).
Fail Check is_vect_witness : forall A P, full A P -> forall i pi, full (vect A i) (is_vect A P i pi).
Fail Check is_dyn_witness.
Check is_zeta_witness : forall A P, full A P -> full (zeta A) (is_zeta A P).
Check is_beta_witness : forall A P, full A P -> full (beta A) (is_beta A P).
Fail Check is_iota_witness.
Check is_large_witness : full large is_large.
