From elpi.apps Require Import derive.eqcorrect.



From elpi.apps Require Import test_derive_stdlib derive.tests.test_eq test_param1 test_param1_functor test_induction test_eqK.

Import test_derive_stdlib.Coverage.
Import tests.test_eq.Coverage.
Import test_param1.Coverage.
Import test_param1_functor.Coverage.
Import test_induction.Coverage.
Import test_eqK.Coverage.

Module Coverage.
Elpi derive.eqcorrect empty.
Elpi derive.eqcorrect unit.
Elpi derive.eqcorrect peano.
Elpi derive.eqcorrect option.
Elpi derive.eqcorrect pair.
Elpi derive.eqcorrect seq.
Elpi derive.eqcorrect box_peano.
Elpi derive.eqcorrect rose.
Elpi derive.eqcorrect rose_p.
Elpi derive.eqcorrect rose_o.
Fail Elpi derive.eqcorrect nest.
Fail Elpi derive.eqcorrect w.
Fail Elpi derive.eqcorrect vect.
Fail Elpi derive.eqcorrect dyn.
Elpi derive.eqcorrect zeta.
Elpi derive.eqcorrect beta.
Fail Elpi derive.eqcorrect iota.
(*
Elpi derive.eqcorrect large.
*)
Elpi derive.eqcorrect prim_int.
Fail Elpi derive.eqcorrect prim_float.
Elpi derive.eqcorrect fo_record.
Elpi derive.eqcorrect pa_record.
Elpi derive.eqcorrect pr_record.
Fail Elpi derive.eqcorrect dep_record.
Elpi derive.eqcorrect enum.
Fail Elpi derive.eqcorrect eq.
Elpi derive.eqcorrect bool.
Fail Elpi derive.eqcorrect sigma_bool.
Fail Elpi derive.eqcorrect ord.
Fail Elpi derive.eqcorrect val.
End Coverage.

Import Coverage.

Local Notation correct X isX F := (forall x, isX x -> eq_axiom_at X F x).

Check empty_eq_correct : correct empty is_empty empty_eq.
Check unit_eq_correct : correct unit is_unit unit_eq.
Check peano_eq_correct : correct peano is_peano peano_eq.
Check option_eq_correct : forall A f, correct (option A) (is_option A (eq_axiom_at A f)) (option_eq A f).
Check pair_eq_correct : forall A f B g, correct (pair A B) (is_pair A (eq_axiom_at A f) B (eq_axiom_at B g)) (pair_eq A f B g).
Check seq_eq_correct : forall A f, correct (seq A) (is_seq A (eq_axiom_at A f)) (seq_eq A f).
Check rose_eq_correct : forall A f, correct (rose A) (is_rose A (eq_axiom_at A f)) (rose_eq A f).
Fail Check nest_eq_correct.
Fail Check w_eq_correct.
Fail Check vect_eq_correct.
Fail Check dyn_eq_correct.
Check zeta_eq_correct : forall A f, correct (zeta A) (is_zeta A (eq_axiom_at A f)) (zeta_eq A f).
Check beta_eq_correct : forall A f, correct (beta A) (is_beta A (eq_axiom_at A f)) (beta_eq A f).
Fail Check iota_eq_correct.
(* Check large_eq_correct : correct large is_large large_eq. *)
Check prim_int_eq_correct.
Fail Check prim_float_eq_correct.
Check fo_record_eq_correct : correct fo_record is_fo_record fo_record_eq.
Check pa_record_eq_correct : forall A f, correct (pa_record A) (is_pa_record A (eq_axiom_at A f)) (pa_record_eq A f).
Check pr_record_eq_correct : forall A f, correct (pr_record A) (is_pr_record A (eq_axiom_at A f)) (pr_record_eq A f).
Check enum_eq_correct : correct enum is_enum enum_eq.

