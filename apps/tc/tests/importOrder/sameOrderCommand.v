From elpi.apps Require Export tc.

From elpi.apps.tc Extra Dependency "base.elpi" as base.
From elpi.apps.tc Extra Dependency "ho_link.elpi" as ho_link.
From elpi.apps.tc.tests.importOrder Extra Dependency "tc_same_order.elpi" as tc_same_order.

Elpi Command SameOrderImport.
Elpi Accumulate Db tc.db.
Elpi Accumulate File base.
Elpi Accumulate File ho_link.
Elpi Accumulate File tc_same_order.
Elpi Typecheck.

Elpi Override TC TC.Solver All.