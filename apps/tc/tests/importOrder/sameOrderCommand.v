From elpi.apps Require Export tc.

From elpi.apps.tc.elpi Extra Dependency "tc_aux.elpi" as tc_aux.
From elpi.apps.tc.elpi Extra Dependency "link.elpi" as link.
From elpi.apps.tc.elpi Extra Dependency "tc_same_order.elpi" as tc_same_order.
From elpi.apps.tc.elpi Extra Dependency "unif.elpi" as unif.
From elpi.apps.tc.elpi Extra Dependency "compile_goal.elpi" as compile_goal.

Set Warnings "+elpi".
Elpi Command SameOrderImport.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File tc_aux.
Elpi Accumulate File unif.
Elpi Accumulate File compile_goal.
Elpi Accumulate File link.
Elpi Accumulate File tc_same_order.


Elpi TC Solver Override TC.Solver All.