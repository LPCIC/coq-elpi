From elpi.apps.tc.tests Require Import stdppInj.
Elpi TC_solver. Set TimeRefine. Set TimeTC. Set Debug "elpitime". 
Elpi Accumulate TC_solver lp:{{
  :after "firstHook"
  tc-Inj A B RA RB {{@compose lp:A lp:B lp:C lp:LC lp:RC}} Sol :- !, 
    LC = RC,
    tc-Inj A B RA RB LC Sol1, 
    coq.typecheck LC LCT ok,
    coq.typecheck Sol1 TSol1 ok,
    Sol = {{
      let sol : lp:TSol1 := lp:Sol1 in 
      let fl : lp:LCT := lp:LC in 
      compose_inj lp:RA _ lp:RB fl fl sol sol}}.
}}.
(* Elpi Typecheck TC_solver.  *)

Goal Inj eq eq((compose (compose (compose f f)(compose f f))(compose (compose f f)(compose f f)))). Time apply _. Qed.