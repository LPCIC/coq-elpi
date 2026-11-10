From elpi.apps Require Export tc.

From elpi.apps.tc.elpi Extra Dependency "ho_link.elpi" as ho_link.
From elpi.apps.tc.elpi Extra Dependency "tc_same_order.elpi" as tc_same_order.
From elpi.apps.tc.elpi Extra Dependency "unif.elpi" as unif.
From elpi.apps.tc.elpi Extra Dependency "base.elpi" as base.
From elpi.apps.tc.elpi Extra Dependency "tc.db.elpi" as tcdb.
From elpi.apps.tc.elpi Extra Dependency "tc_aux.elpi" as tc_aux.
From elpi.apps.tc.elpi Extra Dependency "tc_options.db.elpi" as tc_optionsdb.

Set Warnings "+elpi".
Elpi Command SameOrderImport.
Elpi Accumulate Db tc.db.
Elpi Accumulate File ho_link.
Elpi Accumulate File tc_same_order.


Elpi TC Solver Override TC.Solver All.