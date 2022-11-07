From elpi.apps Require Import derive.tag.

From elpi.apps.derive.tests Require Import test_derive_stdlib.
Import test_derive_stdlib.Coverage.

Module Coverage.

Elpi derive.tag empty.
Elpi derive.tag unit.
Elpi derive.tag peano.
Elpi derive.tag option.
Elpi derive.tag pair.
Elpi derive.tag seq.
Elpi derive.tag box_peano.
Elpi derive.tag rose.
Elpi derive.tag rose_p.
Elpi derive.tag rose_o.
Elpi derive.tag nest.
Elpi derive.tag w.
Elpi derive.tag vect.
Elpi derive.tag dyn.
Fail Elpi derive.tag zeta.
Elpi derive.tag beta.
Elpi derive.tag iota.
Elpi derive.tag large.
Elpi derive.tag prim_int.
Elpi derive.tag prim_float.
Elpi derive.tag fo_record.
Elpi derive.tag pa_record.
Elpi derive.tag pr_record.
Elpi derive.tag dep_record.
Elpi derive.tag enum.
Elpi derive.tag eq.
Elpi derive.tag bool.
Elpi derive.tag sigma_bool.
Elpi derive.tag ord.
Elpi derive.tag ord2.
Elpi derive.tag val.
End Coverage.

Import Coverage.
Import PArith.

Local Notation tag X := (X -> positive).

Check empty_tag : tag empty.
Check unit_tag : tag unit.
Check peano_tag : tag peano.
Check option_tag : forall A, tag (option A).
Check pair_tag : forall A B, tag (pair A B).
Check seq_tag : forall A, tag (seq A).
Check rose_tag : forall A, tag (rose A).
Check nest_tag : forall A, tag (nest A).
Check w_tag : forall A, tag (w A).
Check vect_tag : forall A i, tag (vect A i).
Check dyn_tag : tag dyn.
Fail Check zeta_tag : forall A, tag (zeta A).
Check beta_tag : forall A, tag (beta A).
Check iota_tag : tag iota.
Check large_tag : tag large.
Check prim_int_tag : tag prim_int.
Check prim_float_tag : tag prim_float.
Check pa_record_tag : forall A, tag (pa_record A).
Check pr_record_tag : forall A, tag (pr_record A).
Check ord_tag : forall p : peano, tag (ord p).
Check ord2_tag : forall p : peano, tag (ord2 p).
Check val_tag : tag val.
