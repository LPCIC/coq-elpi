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
  tc A _ :- coq.safe-dest-app A (global GR) _, 
    if (instance _ _ GR) fail (coq.say "No instance for the TC" GR, coq.error "No instance for the TC" GR).
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
  pred instances-of-current-section o:list gref.
  :name "myEndHook"
  instances-of-current-section InstsFiltered :-
    coq.env.current-section-path SectionPath,
    std.findall (instance SectionPath _ _) Insts,
    coq.env.section SectionVars,
    std.map-filter Insts (x\r\ sigma X\ instance _ r _ = x, const X = r, not(std.mem SectionVars X)) InstsFiltered.

  % TODO: after coq.env.end-section,
  % the clause marked with @local! of the pred instance are not removed.
  % example in test_API_section
  main _ :- 
    instances-of-current-section InstsFiltered,
    coq.env.end-section,
    std.forall InstsFiltered (add-inst->db []).
}}.
Elpi Typecheck.
Elpi Export myEnd.