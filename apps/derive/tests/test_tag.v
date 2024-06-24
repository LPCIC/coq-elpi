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

Redirect "tmp" Check empty_tag : tag empty.
Redirect "tmp" Check unit_tag : tag unit.
Redirect "tmp" Check peano_tag : tag peano.
Redirect "tmp" Check option_tag : forall A, tag (option A).
Redirect "tmp" Check pair_tag : forall A B, tag (pair A B).
Redirect "tmp" Check seq_tag : forall A, tag (seq A).
Redirect "tmp" Check rose_tag : forall A, tag (rose A).
Redirect "tmp" Check nest_tag : forall A, tag (nest A).
Redirect "tmp" Check w_tag : forall A, tag (w A).
Redirect "tmp" Check vect_tag : forall A i, tag (vect A i).
Redirect "tmp" Check dyn_tag : tag dyn.
Fail Check zeta_tag : forall A, tag (zeta A).
Redirect "tmp" Check beta_tag : forall A, tag (beta A).
Redirect "tmp" Check iota_tag : tag iota.
Redirect "tmp" Check large_tag : tag large.
Redirect "tmp" Check prim_int_tag : tag prim_int.
Redirect "tmp" Check prim_float_tag : tag prim_float.
Redirect "tmp" Check pa_record_tag : forall A, tag (pa_record A).
Redirect "tmp" Check pr_record_tag : forall A, tag (pr_record A).
Redirect "tmp" Check ord_tag : forall p : peano, tag (ord p).
Redirect "tmp" Check ord2_tag : forall p : peano, tag (ord2 p).
Redirect "tmp" Check val_tag : tag val.
