From elpi Require Export tc.

From elpi.apps.tc Extra Dependency "base.elpi" as base.
From elpi.apps.tc Extra Dependency "compiler.elpi" as compiler.
From elpi.apps.tc Extra Dependency "tc_aux.elpi" as tc_aux.
From elpi.apps.tc Extra Dependency "create_tc_predicate.elpi" as create_tc_predicate.

Elpi Command add_instance.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate Db tc.db.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate File compiler.
Elpi Accumulate lp:{{
  main [trm (global Inst), trm (global TC), str Locality, int Prio] :- 
    add-inst Inst TC Locality Prio.

  main [trm (global GR)] :- 
    add-class-gr classic GR.
}}.
Elpi Typecheck.
Elpi Override Register add_instance.
Elpi Override TC TC_solver All.


From elpi.apps.tc.tests.importOrder Extra Dependency "tc_same_order.elpi" as tc_same_order.

Elpi Command SameOrderImport.
Elpi Accumulate Db tc.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_same_order.
Elpi Typecheck.
