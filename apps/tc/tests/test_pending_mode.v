From elpi Require Import tc.

Elpi TC.pending_mode +.
Class C (i : nat).
Instance C0 : C 0. Qed.
Goal exists x, C x. eexists. Fail apply _. Abort.

Class C' (i : nat).
Instance C0' : C' 0. Qed.
Goal exists x, C' x. eexists. apply _. Abort.

Elpi TC.pending_mode +.
Fail Elpi TC.pending_mode +.

Class C'' (i : nat).
Instance C0'' : C'' 0. Qed.
Goal exists x, C'' x. eexists. Fail apply _. Abort.



