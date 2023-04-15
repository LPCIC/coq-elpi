From elpi Require Import elpi.
From elpi.apps.tc Extra Dependency "base.elpi" as base.
From elpi.apps.tc Extra Dependency "compile_ctx.elpi" as compile_ctx.
From elpi.apps.tc Extra Dependency "compiler.elpi" as compiler.
From elpi.apps.tc Extra Dependency "modes.elpi" as modes.
From elpi.apps.tc Extra Dependency "solver.elpi" as solver.

(* Set Warnings "+elpi". *)

Elpi Db tc.db lp:{{
  % contains the instances added to the DB 
  % associated to the list of sections they belong to
  pred instance o:list string, o:gref, o:gref.
  % contains the typeclasses added to the DB
  pred type-classes o:gref.
  
  % contains the clauses to make the TC search
  pred tc o:term, o:term.

  % T cannot be a free variable
  tc T _ :- var T, !, coq.say "fail on flexible function", fail.
  :name "hintHook"
  tc _ _ :- fail.
  :name "leafHook"
  tc _ _ :- fail.
  :name "complexHook"  
  tc _ _ :- fail.


  tc A _ :- coq.safe-dest-app A (global GR) _, 
    if (instance _ _ GR) fail (coq.say "No instance for the TC" GR).
}}.


Elpi Tactic TC_check.
Elpi Accumulate Db tc.db.
Elpi Accumulate File base.
Elpi Accumulate File modes.
Elpi Accumulate File compile_ctx.
Elpi Accumulate File compiler.
Elpi Accumulate File solver.
Elpi Typecheck.

Elpi Command print_instances.
Elpi Accumulate Db tc.db.
Elpi Accumulate lp:{{
  main _ :-
    std.findall (instance _ _ _) Rules,
    coq.say "Instances list is:" Rules.  
}}.
Elpi Typecheck. 

Elpi Command myEnd.
Elpi Accumulate Db tc.db.
Elpi Accumulate File base.
Elpi Accumulate File modes.
Elpi Accumulate File compiler.
Elpi Accumulate lp:{{

  pred instances-of-current-section o:list constant.
  instances-of-current-section InstsFiltered :-
    coq.env.current-section-path SectionPath,
    std.findall (instance SectionPath _ _) Insts,
    std.map Insts (x\r\ instance _ (const r) _ = x) InstNames,
    coq.env.section SectionVars,
    std.filter InstNames (x\ not(std.mem SectionVars x)) InstsFiltered.

  pred add-inst-after-section-end i:constant.
  add-inst-after-section-end GR:-
    % add-inst->db [] (const GR).
    coq.env.current-section-path NewSectionPath,
    Inst = const GR,
    coq.env.typeof Inst Ty,
    get-TC-of-inst-type Ty TC-of-Inst,
    add-tc-db _ (instance NewSectionPath Inst TC-of-Inst),
    compile Ty (global Inst) [] [] C,
    add-tc-db (before "complexHook") C.

  :name "myEndHook"
  main _ :- 
    instances-of-current-section InstsFiltered,
    coq.env.end-section,
    std.forall InstsFiltered add-inst-after-section-end.
}}.
Elpi Typecheck.
Elpi Export myEnd.