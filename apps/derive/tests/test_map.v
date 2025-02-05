From elpi.apps Require Import derive.map.

From elpi.apps.derive.tests Require Import test_derive_corelib.
Import test_derive_corelib.Coverage.

Module Coverage.

Elpi derive.map empty.
Elpi derive.map unit.
Elpi derive.map peano.
Elpi derive.map option.
Elpi derive.map pair.
Elpi derive.map seq.
Elpi derive.map box_peano.
Elpi derive.map rose.
Elpi derive.map rose_p.
Elpi derive.map rose_o.
Fail Elpi derive.map nest.
Fail Elpi derive.map w.
Elpi derive.map vect.
Elpi derive.map dyn.
Elpi derive.map zeta.
Fail Elpi derive.map beta.
Elpi derive.map iota.
Elpi derive.map large.
Elpi derive.map prim_int.
Elpi derive.map prim_float.
Elpi derive.map fo_record.
Elpi derive.map pa_record.
Elpi derive.map pr_record.
Elpi derive.map dep_record.
Elpi derive.map enum.
Fail Elpi derive.map eq.
Elpi derive.map bool.
Elpi derive.map sigma_bool.
Fail Elpi derive.map ord.
Elpi derive.map val.
End Coverage.

Import Coverage.

Local Notation map T := (T -> T).
Local Notation map1 T := (forall X Y, (X -> Y) -> T X%type -> T Y%type).

Redirect "tmp" Check empty_map : map empty.
Redirect "tmp" Check unit_map : map unit.
Redirect "tmp" Check peano_map : map peano.
Redirect "tmp" Check option_map : map1 option.
Redirect "tmp" Check pair_map : forall A B (f : A -> B) C D (g : C -> D), (pair A C) -> (pair B D).
Redirect "tmp" Check seq_map : map1 seq.
Redirect "tmp" Check rose_map : map1 rose.
Fail Check nest_map.
Fail Check w_map.
Redirect "tmp" Check vect_map : forall A B (f : A -> B) i, vect A i -> vect B i.
Redirect "tmp" Check dyn_map : map dyn.
Redirect "tmp" Check zeta_map : forall A B (f : A -> B), zeta A -> zeta B.
Fail Check beta_map.
Redirect "tmp" Check iota_map : map iota.
Redirect "tmp" Check large_map : map large.
Redirect "tmp" Check prim_int_map : map prim_int.
Redirect "tmp" Check prim_float_map : map prim_float.
Redirect "tmp" Check pa_record_map : map1 pa_record.
Redirect "tmp" Check pr_record_map : map1 pr_record.
