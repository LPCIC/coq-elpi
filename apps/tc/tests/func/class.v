From elpi.apps Require Import tc.

Elpi TC.deterministic.

Class C (T : nat).

Instance I1 : C 1. Qed.

Fail Instance I2 : C 1. Qed.
