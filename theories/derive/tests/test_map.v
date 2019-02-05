From elpi Require Import derive.map derive.param1 derive.projK.

From elpi.derive Require Import test_derive_stdlib test_param1.
Import test_derive_stdlib.Coverage.
Import test_param1.Coverage.

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
Fail Elpi derive.map zeta.
Fail Elpi derive.map beta.
Elpi derive.map iota.
Elpi derive.map large.

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
Fail Check zeta_map.
Fail Check beta_map.
Check iota_map : map iota.
Check large_map : map large.

Module Coverage1.

Elpi derive.map is_empty.
Elpi derive.map is_unit.
Elpi derive.map is_peano.
Elpi derive.map is_option.
Elpi derive.map is_pair.
Elpi derive.map is_seq.
Elpi derive.map is_rose.
Elpi derive.map is_nest.
Fail Elpi derive.map is_w.

Elpi derive.map is_vect.
Elpi derive.map is_dyn.
Elpi derive.map is_zeta.
Fail Elpi derive.map is_beta.
Elpi derive.map is_iota.
Fail Timeout 1 Elpi derive.map is_large. (* exponential *)

End Coverage1.

Local Notation func isT := (forall x, isT x -> isT x).
Local Notation func1 isT := (forall A P Q, (forall y : A, P y -> Q y) -> forall x, isT A P x -> isT A Q x).
Local Notation func2 isT := (forall A P Q, (forall y : A, P y -> Q y) -> forall A1 P1 Q1, (forall y : A1, P1 y -> Q1 y) -> forall x, isT A P A1 P1 x -> isT A Q A1 Q1 x).

Import Coverage1.

Check is_empty_map : func is_empty.
Check is_unit_map : func is_unit.
Check is_peano_map : func is_peano.
Check is_option_map : func1 is_option.
Check is_pair_map : func2 is_pair.
Check is_seq_map : func1 is_seq.
Check is_rose_map : func1 is_rose.
Fail Check is_nest_map : func1 is_nest.
Fail Check is_w_map.

Check is_vect_map : forall A P Q, (forall y : A, P y -> Q y) -> forall i p (v : vect A i), is_vect A P i p v -> is_vect A Q i p v.
Check is_dyn_map : func is_dyn.
Check is_zeta_map : func1 is_zeta.
Fail Check is_beta_map.
Check is_iota_map : func is_iota.
Fail Check is_large_map.
