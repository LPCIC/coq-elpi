From elpi Require Import derive.map derive.param1 derive.projK.

From elpi.derive Require Import
  test_derive_stdlib test_param1.

Module Coverage.

Elpi derive.map Coverage.empty.
Elpi derive.map Coverage.unit.
Elpi derive.map Coverage.peano.
Elpi derive.map Coverage.option.
Elpi derive.map Coverage.pair.
Elpi derive.map Coverage.seq.
Elpi derive.map Coverage.tree.
Fail Elpi derive.map Coverage.nest.
Fail Elpi derive.map Coverage.w.
Elpi derive.map Coverage.vect.
Elpi derive.map Coverage.dyn.
Fail Elpi derive.map Coverage.zeta.
Fail Elpi derive.map Coverage.beta.
Elpi derive.map Coverage.iota.
Elpi derive.map Coverage.large.


Elpi derive.map Coverage.is_empty.
Elpi derive.map Coverage.is_unit.
Elpi derive.map Coverage.is_peano.
Elpi derive.map Coverage.is_option.
Elpi derive.map Coverage.is_pair.
Elpi derive.map Coverage.is_seq.
Fail Elpi derive.map Coverage.is_tree.
Elpi derive.map Coverage.is_nest.
Fail Elpi derive.map Coverage.is_w.
Elpi derive.map Coverage.is_vect.
Elpi derive.map Coverage.is_dyn.
Fail Elpi derive.map Coverage.is_zeta.
Fail Elpi derive.map Coverage.is_beta.
Elpi derive.map Coverage.is_iota.
(* Elpi derive.map Coverage.largeR. exponential because of search *) 

End Coverage.

Check Coverage.is_seq_map :
  forall A P Q, (forall x, P x -> Q x) -> forall l, Coverage.is_seq A P l -> Coverage.is_seq A Q l.