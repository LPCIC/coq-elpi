From elpi Require Import elpi.
From elpi.apps.tc Extra Dependency "base.elpi" as base.
From elpi.apps.tc Extra Dependency "compiler.elpi" as compiler.
From elpi.apps.tc Extra Dependency "parserAPI.elpi" as parserAPI.
From elpi.apps.tc Extra Dependency "modes.elpi" as modes.
From elpi.apps.tc Extra Dependency "compile_ctx.elpi" as compile_ctx.
From elpi.apps.tc Extra Dependency "solver.elpi" as solver.

Set Warnings "+elpi".

Elpi Db tc.db lp:{{
  % contains the instances added to the DB 
  % associated to the list of sections they belong to
  % :index (1)
  pred instance o:list string, o:gref, o:gref.
  % contains the typeclasses added to the DB
  :index (3)
  pred type-classes o:gref.
  
  % contains the clauses to make the TC search
  :index(3 5)
  pred tc o:gref, o:term, o:term, o:term.

  % T cannot be a free variable
  tc _ _ T _ :- var T, !, coq.say "fail on flexible function", fail.
  :name "hintHook"
  tc _ _ _ _ :- fail.
  :name "leafHook"
  tc _ _ _ _ :- fail.
  :name "complexHook" 
  tc _ _ _ _ :- fail.

  % tc _ _ A _ :- coq.safe-dest-app A (global GR) _, 
  %   if (instance _ _ GR) fail (coq.say "No instance for the TC" GR, fail).
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

Elpi Command MySectionEnd.
Elpi Accumulate Db tc.db.
Elpi Accumulate File base.
Elpi Accumulate File modes.
Elpi Accumulate File compiler.
Elpi Accumulate lp:{{
  pred instances-of-current-section o:list gref.
  :name "MySectionEndHook"
  instances-of-current-section InstsFiltered :-
    coq.env.current-section-path SectionPath,
    std.findall (instance SectionPath _ _) Insts,
    coq.env.section SectionVars,
    std.map-filter Insts (x\r\ sigma X\ instance _ r _ = x, const X = r, not(std.mem SectionVars X)) InstsFiltered.

  main _ :- 
    instances-of-current-section InstsFiltered,
    coq.env.end-section,
    std.forall {std.rev InstsFiltered} (add-inst->db [] tt).
}}.
Elpi Typecheck.

Elpi Command AddAllInstances.
Elpi Accumulate Db tc.db.
Elpi Accumulate File base.
Elpi Accumulate File modes.
Elpi Accumulate File compiler.
Elpi Accumulate lp:{{  
  main L :- 
    args->str-list L L1,
    std.forall {coq.TC.db-tc} (x\ if (const _ = x) (add-tc-or-inst-gr [] L1 [x]) true).
}}.
Elpi Typecheck.

Elpi Command AddInstances.
Elpi Accumulate Db tc.db.
Elpi Accumulate File base.
Elpi Accumulate File modes.
Elpi Accumulate File compiler.
Elpi Accumulate File parserAPI.
Elpi Accumulate lp:{{
  % The main of the Command
  main Arguments :- 
    parse Arguments Res, run-command Res.
}}.
Elpi Typecheck.

Elpi Export AddInstances.
Elpi Export AddAllInstances.
Elpi Export MySectionEnd.
