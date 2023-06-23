From elpi Require Import elpi.
From elpi.apps.tc Extra Dependency "base.elpi" as base.
From elpi.apps.tc Extra Dependency "compiler.elpi" as compiler.
From elpi.apps.tc Extra Dependency "parser_addInstances.elpi" as parser_addInstances.
From elpi.apps.tc Extra Dependency "modes.elpi" as modes.
From elpi.apps.tc Extra Dependency "alias.elpi" as alias.
From elpi.apps.tc Extra Dependency "solver.elpi" as solver.
From elpi.apps.tc Extra Dependency "rewrite_forward.elpi" as rforward.
From elpi.apps.tc Extra Dependency "tc_aux.elpi" as tc_aux.

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
  :index (3)
  pred tc o:gref, o:term, o:term.

  pred hook.
  :name "firstHook" hook.
  :name "lastHook" hook.
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
Elpi Accumulate File tc_aux.
Elpi Accumulate lp:{{
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
Elpi Accumulate File tc_aux.
Elpi Accumulate lp:{{  
  main L :- 
    std.time (
      args->str-list L L1,
      std.forall {coq.TC.db-tc} (x\ add-tc-or-inst-gr [] L1 [x])) T,
    if (coq.option.get ["TimeAddInstances"] (coq.option.bool tt))
      (coq.say "Add instance Time" T) true.
}}.
Elpi Typecheck.

Elpi Command AddInstances.
Elpi Accumulate Db tc.db.
Elpi Accumulate File base.
Elpi Accumulate File modes.
Elpi Accumulate File compiler.
Elpi Accumulate File parser_addInstances.
Elpi Accumulate File tc_aux.
Elpi Accumulate lp:{{
  % The main of the Command
  main Arguments :- 
    std.time (parse Arguments Res, run-command Res) T,
    if (coq.option.get ["TimeAddInstances"] (coq.option.bool tt))
      (coq.say "Add instance all Time" T) true.
}}.
Elpi Typecheck.
Elpi Query lp:{{
  coq.option.add ["TimeAddInstances"] (coq.option.bool ff) ff.
}}.
Elpi Typecheck.

Elpi Command AddHooks.
Elpi Accumulate Db tc.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate lp:{{
  main [int N] :-
    IterNb is (N + 1) * 2,
    for-loop0 IterNb (x\ sigma HookNameProv HookName Div Mod\ 
      Div is x div 2, Mod is x mod 2,
      HookNameProv is int_to_string Div,
      if (Mod = 0) (HookName = HookNameProv) (HookName is HookNameProv ^ "_complex"),
      @global! => add-tc-db HookName (after "firstHook") hook
    ).
}}.
Elpi Typecheck.

Elpi AddHooks 1000.
Elpi Typecheck.

Elpi Command AddForwardRewriting.
Elpi Accumulate Db tc.db.
Elpi Accumulate File rforward.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate lp:{{
  main L :- 
    std.forall {args->str-list L} add-lemma->forward.
}}.
Elpi Typecheck.

Elpi Command AddAlias.
Elpi Accumulate Db tc.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File alias.
Elpi Accumulate lp:{{
  main [trm New, trm Old] :-
    add-tc-db _ _ (alias New Old).
}}.
Elpi Typecheck.

Elpi Tactic TC_solver.
Elpi Accumulate Db tc.db.
Elpi Accumulate File rforward.
Elpi Accumulate File base.
Elpi Accumulate File modes.
Elpi Accumulate File alias.
Elpi Accumulate File compiler.
Elpi Accumulate File solver.
Elpi Accumulate File tc_aux.
Elpi Query lp:{{
  coq.option.add ["UseRemoveEta"] (coq.option.bool tt) ff,
  coq.option.add ["TimeTC"] (coq.option.bool ff) ff,
  coq.option.add ["TimeRefine"] (coq.option.bool ff) ff.
}}.
Elpi Typecheck.

Elpi Export AddInstances.
Elpi Export AddAllInstances.
Elpi Export MySectionEnd.
