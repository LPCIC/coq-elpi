From elpi.apps Require Import derive.eqType_ast.

From elpi.apps.derive.tests Require Import test_derive_corelib.
Import test_derive_corelib.Coverage.

Module Coverage.
Elpi derive.eqType.ast empty.
Elpi derive.eqType.ast unit.
Elpi derive.eqType.ast peano.
Elpi derive.eqType.ast option.
Elpi derive.eqType.ast pair.
Elpi derive.eqType.ast seq.
Elpi derive.eqType.ast box_peano.
Elpi derive.eqType.ast rose.
Elpi derive.eqType.ast rose_p.
Elpi derive.eqType.ast rose_o.
Fail Elpi derive.eqType.ast nest.
Fail Elpi derive.eqType.ast w.
Fail Elpi derive.eqType.ast vect.
Fail Elpi derive.eqType.ast dyn.
Fail Elpi derive.eqType.ast zeta.
Elpi derive.eqType.ast beta.
Fail Elpi derive.eqType.ast iota.
Elpi derive.eqType.ast large.
Elpi derive.eqType.ast prim_int.
Fail Elpi derive.eqType.ast prim_float.
Elpi derive.eqType.ast prim_string.
Elpi derive.eqType.ast fo_record.
Elpi derive.eqType.ast pa_record.
Elpi derive.eqType.ast pr_record.
Fail Elpi derive.eqType.ast dep_record.
Elpi derive.eqType.ast enum.
Elpi derive.eqType.ast bool.
Fail Elpi derive.eqType.ast eq.
Elpi derive.eqType.ast sigma_bool.
Elpi derive.eqType.ast sigma_bool2.
Elpi derive.eqType.ast ord.
Elpi derive.eqType.ast ord2.
Elpi derive.eqType.ast val.
End Coverage.
Import Coverage.

Inductive F1 := | K1 : (peano -> peano) -> F1.
Fail Elpi derive.eqType.ast F1.

Inductive F2 := | K2 : F1 -> F2.
Fail Elpi derive.eqType.ast F2.

Inductive S1 (x : F1) := | D1.
Elpi derive.eqType.ast S1.


Inductive S2 (x : F1) := | D2 : S1 x -> S2.
Elpi derive.eqType.ast S2.

Inductive S3 (f : peano -> peano) := | D3 x : f x = x -> S3.
Elpi derive.eqType.ast S3.




