From elpi Require Import elpi.
From elpi.apps.tc Extra Dependency "base.elpi" as base.
From elpi.apps.tc Extra Dependency "compiler.elpi" as compiler.
From elpi.apps.tc Extra Dependency "parserAPI.elpi" as parserAPI.
From elpi.apps.tc Extra Dependency "modes.elpi" as modes.
From elpi.apps.tc Extra Dependency "compile_ctx.elpi" as compile_ctx.
From elpi.apps.tc Extra Dependency "solver.elpi" as solver.
From elpi.apps.tc Extra Dependency "rewrite_forward.elpi" as rforward.

Set Warnings "+elpi".

Elpi Db tc.db lp:{{

  pred forward i:term, o:term, o:list (pair (list term) term).

  % contains the instances added to the DB 
  % associated to the list of sections they belong to
  % :index (1)
  pred instance o:list string, o:gref, o:gref.
  % contains the typeclasses added to the DB
  :index (3)
  pred type-classes o:gref.
  
  % contains the clauses to make the TC search
  % :index(3 5)
  % pred tc o:gref, o:term, o:term, o:term.
  :index (3)
  pred tc o:gref, o:term, o:term.
  % pred tc o:term, o:term.
  tc _ T _ :- var T, !, coq.say "fail on flexible function", fail.

  pred hook.
  
  :name "first"
  hook.

  pred last-no-error i:list A, o:A.
  last-no-error A B :-
    (std.last [] _ :- !, fail) => std.last A B.

  pred remove-eta i:term, o:term.
  remove-eta A B :- !,
    (pi F Bo\ (copy (fun _ _ Bo) (app F) :-
      pi x\ sigma L\
        (Bo x) = app L,
        last-no-error L x,
        std.drop-last 1 L F)
    ) => copy A B. 

  :name "hintHook"
  hook.

  % TODO: here we make eta reduction on the term received in input
  tc A B S :-
    remove-eta B B',
    not (same_term B B'), !,
    tc A B' S.
  :name "leafHook"
  hook.
  :name "withPremisesHook"
  hook.
  :name "complexHook" 
  hook.
}}.

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
    std.forall {coq.TC.db-tc} (x\ add-tc-or-inst-gr [] L1 [x]).
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

Elpi Command AddHooks.
Elpi Accumulate Db tc.db.
Elpi Accumulate File base.
Elpi Accumulate lp:{{
  main [int N] :-
    for-loop0 {calc (N + 1)} (x\ sigma S\ 
    S is int_to_string x, @global! => add-tc-db S (after "withPremisesHook") hook).
}}.
Elpi Typecheck.

Elpi AddHooks 1000.
Elpi Typecheck.
Elpi Command AddForwardRewriting.
Elpi Accumulate Db tc.db.
Elpi Accumulate File rforward.
Elpi Accumulate File base.
Elpi Accumulate lp:{{
  main L :- 
    std.forall {args->str-list L} add-lemma->forward.
}}.
Elpi Typecheck.

Elpi Tactic TC_solver.
Elpi Accumulate Db tc.db.
Elpi Accumulate File rforward.
Elpi Accumulate File base.
Elpi Accumulate File modes.
Elpi Accumulate File compiler.
Elpi Accumulate File compile_ctx.
Elpi Accumulate File solver.
Elpi Typecheck.

Elpi Export AddInstances.
Elpi Export AddAllInstances.
Elpi Export MySectionEnd.
