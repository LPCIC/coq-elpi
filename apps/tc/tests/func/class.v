From elpi.apps Require Import tc.

Elpi TC.deterministic.
Elpi TC.Pending_mode "+".

Class C (T : nat).

Instance I1 : C 1. Qed.

Instance I2 : C 1. Fail Qed. Abort.
