From elpi.apps Require Import test_derive_stdlib derive.eq.

Import test_derive_stdlib.Coverage.

Module Coverage.
Elpi derive.eq empty.
Elpi derive.eq unit.
Elpi derive.eq peano.
Elpi derive.eq option.
Elpi derive.eq pair.
Elpi derive.eq seq.
Elpi derive.eq rose.
Fail Elpi derive.eq nest.
Fail Elpi derive.eq w.
Elpi derive.eq vect.
Fail Elpi derive.eq dyn.
Elpi derive.eq zeta.
Elpi derive.eq beta.
Fail Elpi derive.eq iota.
Elpi derive.eq large.
End Coverage.

Import Coverage.

Notation eq_test T := (T -> T -> bool).

Check empty_eq   : eq_test empty.
Check unit_eq    : eq_test unit.
Check peano_eq   : eq_test peano.
Check option_eq  : forall A, eq_test A -> eq_test (option A).
Check pair_eq    : forall A, eq_test A -> forall B, eq_test B -> eq_test (pair A B).
Check seq_eq     : forall A, eq_test A -> eq_test (seq A).
Check rose_eq    : forall A, eq_test A -> eq_test (rose A).
Fail Check nest_eq.
Fail Check w_eq.
Check vect_eq    : forall A, eq_test A -> forall i, eq_test (vect A i).
Fail Check dyn_eq.
Check zeta_eq : forall A, eq_test A -> eq_test (zeta A).
Check beta_eq : forall A, eq_test A -> eq_test (beta A).
Fail Check iota_eq : eq_test iota.
Check large_eq   : eq_test large. 