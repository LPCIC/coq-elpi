
From elpi.apps Require Import derive.lens_laws.

From elpi.apps Require Import test_derive_stdlib test_lens.

Import test_derive_stdlib.Coverage.
Import test_lens.Coverage.

(* coverage *)
Module Coverage.
Elpi derive.lens_laws fo_record.
Elpi derive.lens_laws pa_record.
Elpi derive.lens_laws pr_record.
End Coverage.

Import Coverage.

Check _f1_law1 : law1 _f1.
Check _f2_law1 : law1 _f2.
Check _f3_law1 : forall A, law1 (_f3 A).
Check _f4_law1 : forall A, law1 (_f4 A).
Check _pf3_law1 : forall A, law1 (_pf3 A).
Check _pf4_law1 : forall A, law1 (_pf4 A).

Check _f1_law2 : law2 _f1.
Check _f2_law2 : law2 _f2.
Check _f3_law2 : forall A, law2 (_f3 A).
Check _f4_law2 : forall A, law2 (_f4 A).
Check _pf3_law2 : forall A, law2 (_pf3 A).
Check _pf4_law2 : forall A, law2 (_pf4 A).

Check _f1_law3 : law3 _f1.
Check _f2_law3 : law3 _f2.
Check _f3_law3 : forall A, law3 (_f3 A).
Check _f4_law3 : forall A, law3 (_f4 A).
Check _pf3_law3 : forall A, law3 (_pf3 A).
Check _pf4_law3 : forall A, law3 (_pf4 A).

Check _f1_f2_law4 : law4 _f1 _f2.
Check _f2_f1_law4 : law4 _f2 _f1.
Check _f3_f4_law4 : forall A, law4 (_f3 A) (_f4 A).
Check _f4_f3_law4 : forall A, law4 (_f4 A) (_f3 A).
Check _pf3_pf4_law4 : forall A, law4 (_pf3 A) (_pf4 A).
Check _pf4_pf3_law4 : forall A, law4 (_pf4 A) (_pf3 A).

