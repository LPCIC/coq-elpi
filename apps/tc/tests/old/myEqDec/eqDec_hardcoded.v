From elpi Require Import elpi.
From elpi.apps Require Export tc.myEqDec.eqDec_proof.

Set Typeclasses Debug.

Elpi Tactic HS_EqDec.
Elpi Debug "DEBUG1!" "DEBUG2!".
Elpi Accumulate lp:{{
  :if "DEBUG1" msolve L _ :- coq.say "This is L" L, fail.

  msolve L N :-
    std.rev L LR, coq.ltac.all (coq.ltac.open solve) LR N.

  solve (goal _ _ Ty Sol _ as G) GL :- var Sol,
    (if (tc Ty X) 
      (refine X G GL) 
      (GL = [seal G])).
  :if "DEBUG2" tc X Y :- coq.say "Attempt tc" X Y, fail.

  pred tc i:term, o:term.
  tc {{ EqDec lp:A }} _ :- var A, !.

  tc T _ :- var T, !, coq.say "fail on flexible", fail.
  tc {{ EqDec unit }} {{ eq_unit }}.
  tc {{ EqDec nat }} {{ eq_nat }}.
  tc {{ EqDec bool }} {{ eq_bool }}.
  tc {{ EqDec (list lp:T) }} {{ @eq_list lp:T lp:EqD }} :- tc {{ EqDec lp:T }} EqD. 
  tc {{ EqDec (@bin lp:T) }} {{ @eq_bin lp:T lp:EqD }} :- tc {{ EqDec lp:T }} EqD. 
  tc {{ EqDec (prod lp:T1 lp:T2) }} {{ @eq_prod lp:T1 lp:EqDec1 lp:T2 lp:EqDec2 }} :-
    tc {{ EqDec lp:T1 }} EqDec1, tc {{ EqDec lp:T2 }} EqDec2.
  tc {{ EqDec (@bin2 lp:T1 lp:T2) }} {{ @eq_bin2 lp:T1 lp:EqDec1 lp:T2 lp:EqDec2 }} :-
    tc {{ EqDec lp:T1 }} EqDec1, tc {{ EqDec lp:T2 }} EqDec2.
  tc {{ EqDec (@letter lp:T) }} {{ @eq_letter lp:T lp:EqD }} :-
    tc {{ EqDec lp:T }} EqD. 
}}.
Elpi Typecheck.

Elpi Override TC HS_EqDec Only EqDec.

Elpi Print HS_EqDec.
Elpi Trace Browser.

Check (fun a b : _ => a == b).
