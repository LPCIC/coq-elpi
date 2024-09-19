From elpi.apps Require Import tc. 
Elpi TC Solver Override TC.Solver All.

Elpi TC.AddHook after 1000 1513.
Elpi TC.AddHook before 1513 1512.

Class A (n : nat). 
Instance Inst1 : A 3 | 1513. Qed.
Instance Inst2 : A 100 | 1512. Qed.

Elpi Query TC.Solver lp:{{
  sigma InstL GrefL\
  std.findall (tc.instance _ _ {{:gref A}} _) InstL, 
  std.map InstL (x\r\ x = tc.instance _ r _ _) GrefL, 
  GrefL = [{{:gref Inst2}}, {{:gref Inst1}}].
}}.


