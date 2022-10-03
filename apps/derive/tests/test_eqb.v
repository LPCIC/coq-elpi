From elpi.apps Require Import derive.eqb.

From elpi.apps.derive.tests Require Import test_derive_stdlib test_eqType_ast test_tag test_fields.
Import test_derive_stdlib.Coverage test_eqType_ast.Coverage test_tag.Coverage test_fields.Coverage.
    
Module Coverage.
Elpi derive.eqb empty.
Elpi derive.eqb unit.
Elpi derive.eqb peano.
Elpi derive.eqb option.
Elpi derive.eqb pair.
Elpi derive.eqb seq.
Elpi derive.eqb box_peano.
Elpi derive.eqb rose.
Elpi derive.eqb rose_p.
Elpi derive.eqb rose_o.
Fail Elpi derive.eqb nest.
Fail Elpi derive.eqb w.
Fail Elpi derive.eqb vect.
Fail Elpi derive.eqb dyn.
Fail Elpi derive.eqb zeta.
Elpi derive.eqb beta.
Fail Elpi derive.eqb iota.
(* slow
Elpi derive.eqb large.
*)
Elpi derive.eqb prim_int.
Fail Elpi derive.eqb prim_float.
Elpi derive.eqb fo_record.
Elpi derive.eqb pa_record.
Elpi derive.eqb pr_record.
Fail Elpi derive.eqb dep_record.
Elpi derive.eqb enum.
Fail Elpi derive.eqb eq.
Elpi derive.eqb bool.
Elpi derive.eqb sigma_bool.
Elpi derive.eqb ord.
Elpi derive.eqb ord2.
Elpi derive.eqb val.

End Coverage.
Import Coverage.
Import PArith.

Notation eq_test T := (T -> T -> bool).
Notation eq_test2 T1 T2 := (T1 -> T2 -> bool).

Check empty_eqb   : eq_test empty.
Check unit_eqb    : eq_test unit.
Check peano_eqb   : eq_test peano.
Check option_eqb  : forall A, eq_test A -> eq_test (option A).
Check pair_eqb    : forall A, eq_test A -> forall B, eq_test B -> eq_test (pair A B).
Check seq_eqb     : forall A, eq_test A -> eq_test (seq A).
Check rose_eqb    : forall A, eq_test A -> eq_test (rose A).
Fail Check nest_eqb.
(* Check w_eqb.   (* Do something but it is stupide*) *)
Fail Check vect_eqb    : forall A, eq_test A -> forall i, eq_test (vect A i).
Fail Check dyn_eqb.
Fail Check zeta_eqb : forall A, eq_test A -> eq_test (zeta A).
Check beta_eqb : forall A, eq_test A -> eq_test (beta A).
Fail Check iota_eqb : eq_test iota.
(* Check large_eqb   : eq_test large. *)
(* FIXME : the definition of prim_int_eqb_fields*)
Check prim_int_eqb    : eq_test prim_int.
Fail Check prim_float_eqb    : eq_test prim_float.
Check fo_record_eqb : eq_test fo_record.

Check pa_record_eqb : forall A, eq_test A -> eq_test (pa_record A).
Check pr_record_eqb : forall A, eq_test A -> eq_test (pr_record A).
Check enum_eqb : eq_test enum.
Check sigma_bool_eqb : eq_test sigma_bool.
Check ord_eqb : forall p1 p2, eq_test2 (ord p1) (ord p2).
Check ord2_eqb : forall p1 p2, eq_test2 (ord2 p1) (ord2 p2).
Check val_eqb : eq_test val.
