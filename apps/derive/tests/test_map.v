From elpi.apps Require Import derive.map.

From elpi.apps.derive.tests Require Import test_derive_stdlib.
Import test_derive_stdlib.Coverage.

Module Coverage.

Elpi derive.map empty.
Elpi derive.map unit.
Elpi derive.map peano.
Elpi derive.map option.
Elpi derive.map pair.
Elpi derive.map seq.
Elpi derive.map rose.
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

End Coverage.

Import Coverage.

Local Notation map T := (T -> T).
Local Notation map1 T := (forall X Y, (X -> Y) -> T X%type -> T Y%type).

Check empty_map : map empty.
Check unit_map : map unit.
Check peano_map : map peano.
Check option_map : map1 option.
Check pair_map : forall A B (f : A -> B) C D (g : C -> D), (pair A C) -> (pair B D).
Check seq_map : map1 seq.
Check rose_map : map1 rose.
Fail Check nest_map.
Fail Check w_map.
Check vect_map : forall A B (f : A -> B) i, vect A i -> vect B i.
Check dyn_map : map dyn.
Check zeta_map : forall A B (f : A -> B), zeta A -> zeta B.
Fail Check beta_map.
Check iota_map : map iota.
Check large_map : map large.
Check prim_int_map : map prim_int.
Check prim_float_map : map prim_float.

