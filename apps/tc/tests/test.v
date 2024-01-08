From elpi.apps.tc.tests Require Import stdppInj.
Elpi TC.Solver. Set TC Time Refine.
 Set TC Time Instance Search.
Elpi Accumulate TC.Solver lp:{{
  shorten tc-elpi.apps.tc.tests.stdppInj.{tc-Inj}.
  :after "firstHook"
  tc-Inj A B RA RB {{@compose lp:A lp:A lp:A lp:FL lp:FL}} Sol :- !, 
    tc-Inj A B RA RB FL Sol1, 
    coq.typecheck A TA ok,
    coq.typecheck RA TRA ok,
    coq.typecheck FL TFL ok,
    coq.typecheck Sol1 TSol1 ok,
    Sol = {{
      let a : lp:TA := lp:A in 
      let sol : lp:TSol1 := lp:Sol1 in 
      let ra : lp:TRA := lp:RA in 
      let fl : lp:TFL := lp:FL in 
      @compose_inj a a a ra ra ra fl fl sol sol}}.
}}.
Elpi Typecheck TC.Solver. 

Goal Inj eq eq((compose (compose (compose f f )(compose f f ))(compose (compose f f )(compose f f )))). Time apply _. Qed.
