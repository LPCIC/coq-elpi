From Coq Require Import EquivDec Arith Program.Utils.
From elpi Require Import elpi.
Elpi Tactic hardcoded_solver.
Elpi Accumulate lp:{{
  msolve L N :-
    coq.say L,
    std.rev L LR, coq.ltac.all (coq.ltac.open solve) LR N.

  solve (goal _ _ Ty Sol _ as G) GL :- var Sol, !,
    if (tc Ty X) (refine.no_check X G GL) (GL = [seal G]).
  solve _ [].
  :if "DEBUG" tc X Y :- coq.say "Attempt tc" X Y, fail.
  pred tc i:term, o:term.
  tc T _ :- var T, !, coq.say "fail on flexible", fail.
  tc {{ @EqDec nat lp:EQ lp:EQUIV }} {{ nat_eq_eqdec }} :- !,
    EQ = {{ @eq nat }},
    EQUIV = {{ @eq_equivalence nat }}.
  tc {{ @EqDec bool lp:EQ lp:EQUIV }} {{ bool_eqdec }} :- !,
    EQ = {{ @eq bool }},
    EQUIV = {{ @eq_equivalence bool }}.
  tc {{ @EqDec (@prod lp:T1 lp:T2) lp:EQ lp:EQUIV}}
     {{ @prod_eqdec lp:T1 lp:Equiv1 lp:P1 lp:T2 lp:Equiv2 lp:P2 }} :- !,
    EQ = {{@eq (@prod lp:T1 lp:T2)}},
    EQUIV = {{@eq_equivalence (@prod lp:T1 lp:T2)}},
    tc {{@EqDec lp:T1 lp:EQ1 lp:Equiv1}} P1, tc {{@EqDec lp:T2 lp:EQ2 lp:Equiv2}} P2, coq.say "Done".
  tc {{ EqDec lp:T _ _ }} _ :- var T, fail.
  tc T _ :- coq.say "fail" T, fail.
}}.
Elpi Typecheck.

Elpi Tactic compiler_solver.
Elpi Accumulate lp:{{
  msolve L N :-
    std.rev L LR, coq.ltac.all (coq.ltac.open solve) LR N.
  solve (goal _ _ Ty Sol _ as G) GL :- var Sol, !,
    {{EqDec}} = global C, {{Equivalence}} = app [global E|_],
    compile_all [C, E] Clauses,
    (Clauses => if (tc Ty X) (refine.no_check X G GL) (GL = [seal G])).
  solve _ [].
  pred tc o:term, o:term.
  :if "DEBUG" tc X Y :- coq.say "Tc" X Y, fail.
  
  pred compile i:term, i:list prop, i:term, o:prop.
  
  compile (prod _ (app [global S | Args]) F) TODO H (pi x\ C x) :-
    coq.TC.class? S, !,
    pi x\
      compile (F x) [tc (app [global S | Args]) x |TODO] {{ lp:H lp:x }} (C x).
  
  compile (prod _ _ F) TODO H (pi x\ C x) :-
    !,
    pi x\
      compile (F x) TODO {{ lp:H lp:x }} (C x).
  
  compile End TODO HD (tc End HD :- TODO).
  
  pred compile_all i:list gref, o:list prop.
  compile_all Refs Props :-
    std.map Refs coq.TC.db-for LList,
    std.flatten LList Flattened,
    std.map Flattened (x\y\ x = tc-instance y _) NewList,
    std.map NewList 
      (cand\claus\ sigma T\
      coq.env.typeof cand T,
      compile T [] (global cand) claus)
      Props.
  }}.
Elpi Typecheck.



Elpi Override TC compiler_solver.
Check ((fun n m : nat  => n == m)). 
Check (fun b q : bool => b == q).
Check ((fun n m:prod nat bool => n == m)).
