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

Elpi derive.map Coverage.seqR.
Elpi derive.map Coverage.optionR.
Elpi derive.map Coverage.pairR.
Fail Elpi derive.map Coverage.treeR.
Elpi derive.map Coverage.vectR.

End Coverage.

Check Coverage.seqR_map :
  forall A P Q, (forall x, P x -> Q x) -> forall l, Coverage.seqR A P l -> Coverage.seqR A Q l.