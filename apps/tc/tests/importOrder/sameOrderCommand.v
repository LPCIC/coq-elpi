From elpi Require Export compiler.

Elpi Command SameOrderImport.
Elpi Accumulate Db tc.db.
Elpi Accumulate lp:{{
  main _ :-
    std.findall (instance _ _ _) RulesInst,
    coq.TC.db DB_tc-inst,
    std.map RulesInst (x\inst\ instance _Path inst _TC = x) RulesElpi,
    std.map DB_tc-inst (x\inst\ tc-instance inst _ = x) RulesCoq,
    if (RulesElpi = RulesCoq) true (
      coq.error "Error in import order\n" 
      "Expected :" RulesCoq "\nFound   :" RulesElpi).
}}.