
From elpi.apps Require Import derive.lens_laws.

From elpi.apps Require Import test_derive_stdlib test_lens.

Import test_derive_stdlib.Coverage.
Import test_lens.Coverage.

(* coverage *)
Module Coverage.
Elpi derive.lens_laws fo_record.
Elpi derive.lens_laws pa_record.
Elpi derive.lens_laws pr_record.
Elpi derive.lens_laws dep_record.
Elpi derive.lens_laws sigma_bool.
End Coverage.

Import Coverage.

Check _f1_view_set : view_set _f1.
Check _f2_view_set : view_set _f2.
Check _f3_view_set : forall A, view_set (_f3 A).
Check _f4_view_set : forall A, view_set (_f4 A).
Check _pf3_view_set : forall A, view_set (_pf3 A).
Check _pf4_view_set : forall A, view_set (_pf4 A).

Check _f1_set_set : set_set _f1.
Check _f2_set_set : set_set _f2.
Check _f3_set_set : forall A, set_set (_f3 A).
Check _f4_set_set : forall A, set_set (_f4 A).
Check _pf3_set_set : forall A, set_set (_pf3 A).
Check _pf4_set_set : forall A, set_set (_pf4 A).

Check _f1_set_view : set_view _f1.
Check _f2_set_view : set_view _f2.
Check _f3_set_view : forall A, set_view (_f3 A).
Check _f4_set_view : forall A, set_view (_f4 A).
Check _pf3_set_view : forall A, set_view (_pf3 A).
Check _pf4_set_view : forall A, set_view (_pf4 A).

Check _f1_f2_exchange : exchange _f1 _f2.
Check _f2_f1_exchange : exchange _f2 _f1.
Check _f3_f4_exchange : forall A, exchange (_f3 A) (_f4 A).
Check _f4_f3_exchange : forall A, exchange (_f4 A) (_f3 A).
Check _pf3_pf4_exchange : forall A, exchange (_pf3 A) (_pf4 A).
Check _pf4_pf3_exchange : forall A, exchange (_pf4 A) (_pf3 A).

