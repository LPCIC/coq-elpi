From elpi Require Import tc.

Elpi TC.Pending_mode +.
Class C (i : nat).
Instance C0 : C 0. Qed.
Goal exists x, C x. eexists. Fail apply _. Abort.
Elpi Typecheck TC.Solver.
Class C' (i : nat).
Instance C0' : C' 0. Qed.
Goal exists x, C' x. eexists. apply _. Abort.

Elpi TC.Pending_mode +.
Fail Elpi TC.Pending_mode +.

Class C'' (i : nat).
Instance C0'' : C'' 0. Qed.
Goal exists x, C'' x. eexists. Fail apply _. Abort.



