From elpi Require Import elpi.
From elpi.apps.tc Extra Dependency "compile_ctx.elpi" as compile_ctx.
From elpi.apps.tc Extra Dependency "compiler.elpi" as compiler.
From elpi.apps.tc Extra Dependency "modes.elpi" as modes.

(* Set Warnings "+elpi". *)

Elpi Db tc.db lp:{{
  % contains the instances added to the DB
  pred instance o:gref.
  % contains the typeclasses added to the DB
  pred type-classes o:gref.
  % contains the instances declared in a section depending on section
  % variables. These instances are added locally (@local!) and are 
  % removed after quitting the section
  pred queued-instances o:gref.
  
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

  pred solve1 i:goal, o:(list sealed-goal).
  solve1 (goal Ctx _ Ty Sol _ as G) GL :-
    var Sol,
    % Add's the section's definition to the current context
    % in order to add its TC if present
    std.map {coq.env.section} (x\r\ sigma F\ coq.env.typeof (const x) F, r = (decl (global (const x)) _ F)) SectionCtx,
    ctx->clause {std.append Ctx SectionCtx} Clauses,
    Clauses => if (std.spy-do![], tc Ty X) 
      (
        refine X G GL ; 
        coq.say "illtyped solution:" {coq.term->string X}
      ) 
      (GL = [seal G]).

  :if "solve-print-goal"
  solve (goal Ctx _ Ty _ _) _ :-
    coq.say "Ctx" Ctx "Ty" Ty, fail.
  :if "solve-print-type"
  solve (goal _ _ Ty _ _) _ :-
    coq.say "Ty" Ty, fail.
  :if "solve-trace-time"
  solve A B :- !,
    std.spy-do! [std.time (solve1 A B) Time, coq.say Time].
  :if "solve-trace"
  solve A B :- !,
    std.spy-do! [solve1 A B].
  :if "solve-time"
  solve A B :- !,
    std.time (solve1 A B) Time, coq.say Time.
  solve A B :-solve1 A B.
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

Elpi Command myEnd.
Elpi Accumulate Db tc.db.
Elpi Accumulate File modes.
Elpi Accumulate File compiler.
Elpi Accumulate lp:{{
  main _ :- 
    std.findall (queued-instances _) Insts,
    coq.env.end-section,
    std.forall Insts (x\ sigma C Clause Inst Ty\
    queued-instances Inst = x,
    coq.env.typeof Inst Ty,
    compile-no-context Ty (global Inst) [] [] C,
    Clause = clause _ (before "complexHook") C,
    coq.elpi.accumulate _ "tc.db" Clause).
}}.
Elpi Typecheck.
Elpi Export myEnd.