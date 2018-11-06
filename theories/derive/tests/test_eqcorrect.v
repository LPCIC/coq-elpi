From elpi Require Import elpi derive.eq derive.projK derive.isK 
  derive.param1 derive.param1P derive.map
  derive.induction derive.isK derive.projK
  derive.cast derive.bcongr derive.eqK derive.eqcorrect.



From elpi Require Import test_derive_stdlib derive.tests.test_eq test_eqK test_param1 test_map test_induction.

Module Coverage.
Elpi derive.eqcorrect Coverage.empty.
Elpi derive.eqcorrect Coverage.unit.
Elpi derive.eqcorrect Coverage.peano.
Elpi derive.eqcorrect Coverage.option.
Elpi derive.eqcorrect Coverage.pair.
Elpi derive.eqcorrect Coverage.seq.
Elpi derive.eqcorrect Coverage.tree.
Fail Elpi derive.eqcorrect Coverage.nest.
Fail Elpi derive.eqcorrect Coverage.w.
Fail Elpi derive.eqcorrect Coverage.vect.
Fail Elpi derive.eqcorrect Coverage.dyn.
Fail Elpi derive.eqcorrect Coverage.zeta.
Fail Elpi derive.eqcorrect Coverage.beta.
Fail Elpi derive.eqcorrect Coverage.iota.
Elpi derive.eqcorrect Coverage.large.
End Coverage.

