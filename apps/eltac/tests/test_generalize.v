From elpi.apps Require Import eltac.generalize.

Example test_generalize x y (H : x = y) (H1 : 0 <= x) (d := x + 1) (H2 : y = 1) : x + d + y = 2.
Proof.
eltac.generalize (x).
intros x0 T0 T1.
Abort.

