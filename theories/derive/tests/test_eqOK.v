From elpi Require Import elpi derive.eq derive.projK derive.isK 
  derive.param1 derive.param1P derive.map
  derive.induction derive.isK derive.projK
  derive.cast derive.bcongr derive.eqK derive.eqOK.



From elpi Require Import test_derive_stdlib derive.tests.test_eq test_eqK test_param1 test_map test_induction.

Module Coverage.
Elpi derive.eqOK Coverage.empty.
Elpi derive.eqOK Coverage.unit.
Elpi derive.eqOK Coverage.peano.
Elpi derive.eqOK Coverage.option.
Elpi derive.eqOK Coverage.pair.
Elpi derive.eqOK Coverage.seq.
Elpi derive.eqOK Coverage.tree.
Fail Elpi derive.eqOK Coverage.nest.
Fail Elpi derive.eqOK Coverage.w.
Fail Elpi derive.eqOK Coverage.vect.
Fail Elpi derive.eqOK Coverage.dyn.
Fail Elpi derive.eqOK Coverage.zeta.
Fail Elpi derive.eqOK Coverage.beta.
Fail Elpi derive.eqOK Coverage.iota.
Elpi derive.eqOK Coverage.large.
End Coverage.

