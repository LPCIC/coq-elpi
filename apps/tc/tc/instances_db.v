From elpi Require Import elpi.
From elpi.apps.tc Extra Dependency "compile_ctx.elpi" as compile_ctx.
From elpi.apps.tc Extra Dependency "compiler.elpi" as compiler.
From elpi.apps.tc Extra Dependency "modes.elpi" as modes.

Set Warnings "+elpi".

Elpi Db tc.db lp:{{
  % contains the instances added to the DB
  pred instance o:gref.
  
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
}}.


Elpi Tactic TC_check.
Elpi Accumulate Db tc.db.
Elpi Accumulate File modes.
Elpi Accumulate File compile_ctx.
Elpi Accumulate File compiler.

Elpi Accumulate lp:{{
  msolve L N :-
    std.rev L LR, coq.ltac.all (coq.ltac.open solve) LR N.

  :if "debug"
  solve (goal Ctx _ Ty Sol _) _ :- 
    coq.say "Ctx is" Ctx "\nTy is" Ty "\nSol is" Sol, fail.
  solve (goal Ctx _ Ty Sol _ as G) GL :- 
    var Sol,
    ctx->clause Ctx Clauses,
    Clauses => if (tc Ty X) 
      (refine X G GL ; coq.say "illtyped solution:" {coq.term->string X}) 
      (GL = [seal G]).
}}.
Elpi Typecheck.

Elpi Command print_instances.
Elpi Accumulate Db tc.db.
Elpi Accumulate lp:{{
  main _ :-
    std.findall (instance _) Rules,
    coq.say "Instances list is:" Rules.  
}}.
Elpi Typecheck.