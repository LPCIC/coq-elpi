From elpi Require Import elpi.

Elpi Tactic data_passing.
Elpi Accumulate lp:{{
  shorten coq.ltac.{ open , thenl , set-goal-arguments }.

  pred dup i:goal, o:list sealed-goal.
  dup (goal _ _ _ _ [trm T] as G) GS :-
    refine {{ _ lp:T }} G GL,
    std.map GL (set-goal-arguments [trm T] G) GS. % passing an argument to subgoals
    

  pred clear i:goal, o:list sealed-goal.
  clear (goal C _ _ E [trm T]) _ :-
    std.map C (x\r\x = decl r _ _) Names,
    std.filter Names (x\not (x = T)) InScope,
    prune E InScope.

  solve (goal _ _ _ _ [trm T] as G) GL :- name T,
    thenl [open dup, open clear] (seal G) GL.

}}.
Elpi Typecheck.

Goal forall z x : nat, True.
intros z x.
elpi data_passing (x).
Fail Check x.
Check z.
intro y.
Abort.


(* Abstract *)

Ltac horror := abstract (exact I).

Elpi Command define_it.
Elpi Accumulate lp:{{
  main [] :-
    coq.elaborate-skeleton _ {{ True }} Bo ok,
    coq.ltac.collect-goals Bo [SealedGoal] [],
    coq.ltac.open (coq.ltac.call "horror" []) SealedGoal [],
    coq.locate "elpi_subproof" _,
    coq.env.add-const "it" Bo _ @transparent! C_.

}}.
Elpi Typecheck.
Elpi define_it.

Print it.
About it.

Print elpi_subproof.
About elpi_subproof.

Print Assumptions it.
