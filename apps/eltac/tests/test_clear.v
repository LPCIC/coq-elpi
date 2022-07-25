From elpi.apps Require Import eltac.clear.

Example test_generalize_dependent x y (H : x = y) (H1 : 0 <= x) (d := x + 1) (H2 : y = 1) (w := 3): x + d + y = 2.
Proof.
generalize dependent x.
Fail eltac.clear x.
eltac.clear H2.
Fail match goal with Hyp : y = 1 |- _ => idtac end.
intros.
eltac.clearbody d w.
Fail unfold d.
Check d.
Abort.
