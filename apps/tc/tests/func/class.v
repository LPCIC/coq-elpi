From elpi.apps Require Import tc.

Elpi TC.deterministic.

Class C (T : nat).

Instance I1 : C 1. Qed.
Instance I2 : C 1. Qed.

Elpi Print TC.Solver "elpi.apps.tc.examples/TC.Solver".
