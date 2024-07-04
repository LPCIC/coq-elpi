From elpi.apps Require Export tc.

From elpi.apps.tc.elpi Extra Dependency "base.elpi" as base.
From elpi.apps.tc.elpi Extra Dependency "ho_link.elpi" as ho_link.
From elpi.apps.tc.tests.importOrder Extra Dependency "tc_same_order.elpi" as tc_same_order.
From elpi.apps.tc.elpi Extra Dependency "unif.elpi" as unif.

Set Warnings "+elpi".
Elpi Command SameOrderImport.
Elpi Accumulate Db tc.db.
Elpi Accumulate File base.
Elpi Accumulate File unif.
Elpi Accumulate File ho_link.
Elpi Accumulate File tc_same_order.
Elpi Typecheck.

Elpi TC Solver Override TC.Solver All.