From elpi.apps Require Import test_derive_corelib derive.eq.

Import test_derive_corelib.Coverage.

Module Coverage.
Elpi derive.eq empty.
Elpi derive.eq unit.
Elpi derive.eq peano.
Elpi derive.eq option.
Elpi derive.eq pair.
Elpi derive.eq seq.
Elpi derive.eq box_peano.
Elpi derive.eq rose.
Elpi derive.eq rose_p.
Elpi derive.eq rose_o.
Fail Elpi derive.eq nest.
Fail Elpi derive.eq w. (* expected *)
Elpi derive.eq vect.
Fail Elpi derive.eq dyn. (* expected *)
Elpi derive.eq zeta.
Elpi derive.eq beta.
Fail Elpi derive.eq iota.
Elpi derive.eq large.
Elpi derive.eq prim_int.
Elpi derive.eq prim_float.
Elpi derive.eq prim_string.
Elpi derive.eq fo_record.
Elpi derive.eq pa_record.
Elpi derive.eq pr_record.
Fail Elpi derive.eq dep_record.
Elpi derive.eq enum.
Fail Elpi derive.eq eq.
Elpi derive.eq bool.
Fail Elpi derive.eq sigma_bool.
Fail Elpi derive.eq ord.
Fail Elpi derive.eq val.
End Coverage.

Import Coverage.

Notation eq_test T := (T -> T -> bool).

Redirect "tmp" Check empty_eq   : eq_test empty.
Redirect "tmp" Check unit_eq    : eq_test unit.
Redirect "tmp" Check peano_eq   : eq_test peano.
Redirect "tmp" Check option_eq  : forall A, eq_test A -> eq_test (option A).
Redirect "tmp" Check pair_eq    : forall A, eq_test A -> forall B, eq_test B -> eq_test (pair A B).
Redirect "tmp" Check seq_eq     : forall A, eq_test A -> eq_test (seq A).
Redirect "tmp" Check rose_eq    : forall A, eq_test A -> eq_test (rose A).
Fail Check nest_eq.
Fail Check w_eq.
Redirect "tmp" Check vect_eq    : forall A, eq_test A -> forall i, eq_test (vect A i).
Fail Check dyn_eq.
Redirect "tmp" Check zeta_eq : forall A, eq_test A -> eq_test (zeta A).
Redirect "tmp" Check beta_eq : forall A, eq_test A -> eq_test (beta A).
Fail Check iota_eq : eq_test iota.
Redirect "tmp" Check large_eq   : eq_test large.
Redirect "tmp" Check prim_int_eq    : eq_test prim_int.
Redirect "tmp" Check prim_float_eq    : eq_test prim_float.
Redirect "tmp" Check fo_record_eq : eq_test fo_record.
Redirect "tmp" Check pa_record_eq : forall A, eq_test A -> eq_test (pa_record A).
Redirect "tmp" Check pr_record_eq : forall A, eq_test A -> eq_test (pr_record A).
Redirect "tmp" Check enum_eq : eq_test enum.
