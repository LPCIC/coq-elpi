From elpi.tc.eqDec Require Import tc_lib_hardcoded.

Elpi Override TC hardcoded_solver.
Check ((fun n m : nat  => n == m)).
Compute (true == false). 
Check (fun b q : bool => b == q).
Check ((fun n m:prod nat bool => n == m)).