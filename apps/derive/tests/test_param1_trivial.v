From elpi.apps Require Import derive.param1_trivial.

From elpi.apps Require Import test_derive_corelib test_param1 test_param1_congr.
Import derive.param1. (* for is_eq *)
Import test_derive_corelib.Coverage.
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
Elpi derive.param1.trivial is_prim_string.
Elpi derive.param1.trivial is_fo_record.
Elpi derive.param1.trivial is_pa_record.
Elpi derive.param1.trivial is_pr_record.
Fail Elpi derive.param1.trivial is_dep_record.
Elpi derive.param1.trivial is_enum.
(* Elpi derive.param1.trivial is_bool. done in param1_trivial.v *)
(*
Elpi derive.param1.trivial is_eq. (* ad-hoc *)
*)
Elpi derive.param1.trivial is_sigma_bool.
Elpi derive.param1.trivial is_sigma_bool2.
Elpi derive.param1.trivial is_ord.
Elpi derive.param1.trivial is_ord2.
Elpi derive.param1.trivial is_val.

End Coverage.

Import Coverage.
Export param1_trivial.exports. (* for is_bool, done in param1_trivial.v *)

Redirect "tmp" Check is_empty_trivial : trivial empty is_empty.
Redirect "tmp" Check is_unit_trivial : trivial unit is_unit.
Redirect "tmp" Check is_peano_trivial : trivial peano is_peano.
Redirect "tmp" Check is_option_trivial : forall A P, trivial A P -> trivial (option A) (is_option A P).
Redirect "tmp" Check is_pair_trivial : forall A P, trivial A P -> forall B Q, trivial B Q -> trivial (pair A B) (is_pair A P B Q).
Redirect "tmp" Check is_seq_trivial : forall A P, trivial A P -> trivial (seq A) (is_seq A P).
Redirect "tmp" Check is_rose_trivial : forall A P, trivial A P -> trivial (rose A) (is_rose A P).
Fail Check is_nest_trivial.
Fail Check is_w_trivial : forall A P, trivial A P -> trivial (w A) (is_w A P).
Fail Check is_vect_trivial : forall A P, trivial A P -> forall i pi, trivial (vect A i) (is_vect A P i pi).
Fail Check is_dyn_trivial.
Redirect "tmp" Check is_zeta_trivial : forall A P, trivial A P -> trivial (zeta A) (is_zeta A P).
Redirect "tmp" Check is_beta_trivial : forall A P, trivial A P -> trivial (beta A) (is_beta A P).
Fail Check is_iota_trivial.
Redirect "tmp" Check is_large_trivial : trivial large is_large.
Redirect "tmp" Check is_prim_int_trivial : trivial prim_int is_prim_int.
Redirect "tmp" Check is_prim_float_trivial : trivial prim_float is_prim_float.

Redirect "tmp" Check is_fo_record_trivial : trivial fo_record is_fo_record.
Redirect "tmp" Check is_pa_record_trivial : forall A P, trivial A P -> trivial (pa_record A) (is_pa_record A P).
Redirect "tmp" Check is_pr_record_trivial : forall A P, trivial A P -> trivial (pr_record A) (is_pr_record A P).
Redirect "tmp" Check is_enum_trivial : trivial enum is_enum.
Redirect "tmp" Check is_sigma_bool_trivial : trivial sigma_bool is_sigma_bool.
Redirect "tmp" Check is_ord_trivial : forall p px, trivial (ord p) (is_ord p px).
Redirect "tmp" Check is_ord2_trivial : forall p px, trivial (ord2 p) (is_ord2 p px).
Redirect "tmp" Check is_val_trivial : trivial val is_val.




Redirect "tmp" Check is_empty_inhab : full empty is_empty.
Redirect "tmp" Check is_unit_inhab : full unit is_unit.
Redirect "tmp" Check is_peano_inhab : full peano is_peano.
Redirect "tmp" Check is_option_inhab : forall A P, full A P -> full (option A) (is_option A P).
Redirect "tmp" Check is_pair_inhab : forall A P, full A P -> forall B Q, full B Q -> full (pair A B) (is_pair A P B Q).
Redirect "tmp" Check is_seq_inhab : forall A P, full A P -> full (seq A) (is_seq A P).
Redirect "tmp" Check is_rose_inhab : forall A P, full A P -> full (rose A) (is_rose A P).
Fail Check is_nest_inhab.
Fail Check is_w_inhab : forall A P, full A P -> full (w A) (is_w A P).
Fail Check is_vect_inhab : forall A P, full A P -> forall i pi, full (vect A i) (is_vect A P i pi).
Fail Check is_dyn_inhab.
Redirect "tmp" Check is_zeta_inhab : forall A P, full A P -> full (zeta A) (is_zeta A P).
Redirect "tmp" Check is_beta_inhab : forall A P, full A P -> full (beta A) (is_beta A P).
Fail Check is_iota_inhab.
Redirect "tmp" Check is_large_inhab : full large is_large.
Redirect "tmp" Check is_prim_int_inhab : full prim_int is_prim_int.
Redirect "tmp" Check is_prim_float_inhab : full prim_float is_prim_float.

Redirect "tmp" Check is_fo_record_inhab : full fo_record is_fo_record.
Redirect "tmp" Check is_pa_record_inhab : forall A P, full A P -> full (pa_record A) (is_pa_record A P).
Redirect "tmp" Check is_pr_record_inhab : forall A P, full A P -> full (pr_record A) (is_pr_record A P).
Redirect "tmp" Check is_enum_inhab : full enum is_enum.

Redirect "tmp" Check is_sigma_bool_inhab : full sigma_bool is_sigma_bool.
Redirect "tmp" Check is_ord_inhab : forall p px, full (ord p) (is_ord p px).
Redirect "tmp" Check is_ord2_inhab : forall p px, full (ord2 p) (is_ord2 p px).
Redirect "tmp" Check is_val_inhab : full val is_val.
