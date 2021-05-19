From elpi Require Import elpi.

Elpi Tactic data_passing.
Elpi Accumulate lp:{{

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