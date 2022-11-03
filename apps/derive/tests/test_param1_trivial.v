From elpi.apps Require Import derive.param1_trivial.

From elpi.apps Require Import test_derive_stdlib test_param1 test_param1_congr.
Import derive.param1. (* for is_eq *)
Import test_derive_stdlib.Coverage.
Import test_param1.Coverage.
Import test_param1_congr.Coverage.

Module Coverage.

Elpi derive.param1.trivial is_empty.
Elpi derive.param1.trivial is_unit.
Elpi derive.param1.trivial is_peano.
Elpi derive.param1.trivial is_option.
Elpi derive.param1.trivial is_pair.
Elpi derive.param1.trivial is_seq.
Elpi derive.param1.trivial is_box_peano.
Fail Elpi derive.param1.trivial is_nest.
Elpi derive.param1.trivial is_rose.
Elpi derive.param1.trivial is_rose_p.
Elpi derive.param1.trivial is_rose_o.
Fail Elpi derive.param1.trivial is_w.
Fail Elpi derive.param1.trivial is_vect.
Fail Elpi derive.param1.trivial is_dyn.
Elpi derive.param1.trivial is_zeta.
Elpi derive.param1.trivial is_beta.
Fail Elpi derive.param1.trivial is_iota.
Elpi derive.param1.trivial is_large.
Elpi derive.param1.trivial is_prim_int.
Elpi derive.param1.trivial is_prim_float.
Elpi derive.param1.trivial is_fo_record.
Elpi derive.param1.trivial is_pa_record.
Elpi derive.param1.trivial is_pr_record.
Fail Elpi derive.param1.trivial is_dep_record.
Elpi derive.param1.trivial is_enum.
Elpi derive.param1.trivial is_bool.
(*
Elpi derive.param1.trivial is_eq. (* ad-hoc *)
*)
Elpi derive.param1.trivial is_sigma_bool.
Elpi derive.param1.trivial is_ord.
Elpi derive.param1.trivial is_ord2.
Elpi derive.param1.trivial is_val.


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
Check is_large_trivial : trivial large is_large.
Check is_prim_int_trivial : trivial prim_int is_prim_int.
Check is_prim_float_trivial : trivial prim_float is_prim_float.

Check is_fo_record_trivial : trivial fo_record is_fo_record.
Check is_pa_record_trivial : forall A P, trivial A P -> trivial (pa_record A) (is_pa_record A P).
Check is_pr_record_trivial : forall A P, trivial A P -> trivial (pr_record A) (is_pr_record A P).
Check is_enum_trivial : trivial enum is_enum.
Check is_sigma_bool_trivial : trivial sigma_bool is_sigma_bool.
Check is_ord_trivial : forall p px, trivial (ord p) (is_ord p px).
Check is_ord2_trivial : forall p px, trivial (ord2 p) (is_ord2 p px).
Check is_val_trivial : trivial val is_val.




Check is_empty_witness : full empty is_empty.
Check is_unit_witness : full unit is_unit.
Check is_peano_witness : full peano is_peano.
Check is_option_witness : forall A P, full A P -> full (option A) (is_option A P).
Check is_pair_witness : forall A P, full A P -> forall B Q, full B Q -> full (pair A B) (is_pair A P B Q).
Check is_seq_witness : forall A P, full A P -> full (seq A) (is_seq A P).
Check is_rose_witness : forall A P, full A P -> full (rose A) (is_rose A P).
Fail Check is_nest_witness.
Fail Check is_w_witness : forall A P, full A P -> full (w A) (is_w A P).
Fail Check is_vect_witness : forall A P, full A P -> forall i pi, full (vect A i) (is_vect A P i pi).
Fail Check is_dyn_witness.
Check is_zeta_witness : forall A P, full A P -> full (zeta A) (is_zeta A P).
Check is_beta_witness : forall A P, full A P -> full (beta A) (is_beta A P).
Fail Check is_iota_witness.
Check is_large_witness : full large is_large.
Check is_prim_int_witness : full prim_int is_prim_int.
Check is_prim_float_witness : full prim_float is_prim_float.

Check is_fo_record_witness : full fo_record is_fo_record.
Check is_pa_record_witness : forall A P, full A P -> full (pa_record A) (is_pa_record A P).
Check is_pr_record_witness : forall A P, full A P -> full (pr_record A) (is_pr_record A P).
Check is_enum_witness : full enum is_enum.

Check is_sigma_bool_witness : full sigma_bool is_sigma_bool.
Check is_ord_witness : forall p px, full (ord p) (is_ord p px).
Check is_ord2_witness : forall p px, full (ord2 p) (is_ord2 p px).
Check is_val_witness : full val is_val.
