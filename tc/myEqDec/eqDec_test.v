From elpi.tc Require Import eqDec_proof.
From elpi Require Import elpi.

Check (eq_nat : EqDec nat).

Compute (nil == nil).
Compute ([2; 1] == [1]).
Compute ([true; true] == [true]).
Compute (3 == 4).
Compute (true == false).
Compute (eqb 3 3).
Check (N 3 L).
Check (L == L).
Compute (L1 == L1).
Compute (N1 5 L (N false L L) == N1 5 L (N false L (N true L L))).
Compute (LA (LB 4) == LA (LB 3)).
