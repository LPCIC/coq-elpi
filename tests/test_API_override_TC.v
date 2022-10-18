From elpi Require Import elpi.

From Coq Require Import EquivDec Arith.

Elpi Tactic solver.
Elpi Accumulate lp:{{
  msolve L N :-
    coq.say L,
    std.rev L LR, coq.ltac.all (coq.ltac.open solve) LR N.

  solve (goal _ _ Ty Sol _ as G) GL :- var Sol, !,
    coq.say "inhabit" Ty,
    if (tc Ty X) (refine X G GL) (GL = [seal G]).
  solve _ [].

  pred tc i:term, o:term.
  tc {{ @EqDec nat lp:EQ lp:EQUIV }} {{ Nat.eq_dec }} :- !,
    EQ = {{ @eq nat }},
    EQUIV = {{ @eq_equivalence nat }}.
  tc {{ EqDec lp:T _ _ }} _ :- var T, fail.
  tc T _ :- var T, fail.
  tc T _ :- coq.say "fail" T, fail.

}}.
Elpi Typecheck.

Elpi Override TC solver.
Set Printing All.
Check ((fun n m : nat  => n == m)). , (fun b q : bool => b == q)).
