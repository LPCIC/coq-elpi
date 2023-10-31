From elpi.apps Require Import tc. 
Elpi Override TC TC_solver All.

Elpi AddHook after 1000 1513.
Elpi AddHook before 1513 1512.
Class A (n : nat). 
Instance Inst1 : A 3 | 1513. Qed.
Instance Inst2 : A 100 | 1512. Qed.

Elpi Query TC_solver lp:{{
  sigma InstL GrefL\
  std.findall (instance _ _ {{:gref A}}) InstL, 
  std.map InstL (x\r\ x = instance _ r _) GrefL, 
  GrefL = [{{:gref Inst2}}, {{:gref Inst1}}].
}}.


