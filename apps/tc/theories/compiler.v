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

  pred alias i:term, o:term.
  pred forward i:term, o:term, o:list (pair (list term) term).

  % contains the instances added to the DB 
  % associated to the list of sections they belong to
  % :index (1)
  pred instance o:list string, o:gref, o:gref.
  % contains the typeclasses added to the DB
  :index (3)
  pred type-classes o:gref.
  :index (3)
  pred banned o:gref.
  
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
    % TODO: this is not the full eta-reduaction:
    % eg: λx.f x -> should return f and not app [f]
    % eg: we should eta-reduce (std.map) all the 
    % args of an app: (z\ (f (λx.g x) z)) = (f g)
    % (pi F Bo\ (copy (fun _ _ Bo) R :-
    %   pi x\ sigma L\
    %     (Bo x) = app L,
    %     last-no-error L x,
    %     std.drop-last 1 L F, copy (app F) R)
    % ) => copy A B. 
    (pi F\ copy (fun _ _ x\ (app [F, x])) F) => copy A B.

  :name "hintHook"
  hook.

  % TODO: here we make eta reduction on the term received in input
  :name "remove-eta"
  tc A B S :-
    coq.option.get ["UseRemoveEta"] (coq.option.bool tt),
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
Elpi Accumulate File parserAPI.
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
Elpi Accumulate lp:{{
  main [int N] :-
    IterNb is (N + 1) * 2,
    for-loop0 IterNb (x\ sigma HookNameProv HookName Div Mod\ 
      Div is x div 2, Mod is x mod 2,
      HookNameProv is int_to_string Div,
      if (Mod = 0) (HookName = HookNameProv) (HookName is HookNameProv ^ "_complex"),
      @global! => add-tc-db HookName (after "withPremisesHook") hook
    ).
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

Elpi Command AddAlias.
Elpi Accumulate Db tc.db.
Elpi Accumulate File base.
Elpi Accumulate lp:{{
  main [trm New, trm Old] :-
    add-tc-db _ _ (alias New Old).
}}.

Elpi Tactic TC_solver.
Elpi Accumulate Db tc.db.
Elpi Accumulate File rforward.
Elpi Accumulate File base.
Elpi Accumulate File modes.
Elpi Accumulate File compiler.
Elpi Accumulate File compile_ctx.
Elpi Accumulate File solver.
Elpi Query lp:{{
  coq.option.add ["UseRemoveEta"] (coq.option.bool tt) ff,
  coq.option.add ["TimeTC"] (coq.option.bool ff) ff,
  coq.option.add ["TimeRefine"] (coq.option.bool ff) ff.
}}.
Elpi Typecheck.

Elpi Export AddInstances.
Elpi Export AddAllInstances.
Elpi Export MySectionEnd.