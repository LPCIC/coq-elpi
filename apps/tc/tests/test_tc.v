From elpi.apps Require Import tc.

Elpi Override TC TC_solver All.

Class a (N: nat).
Instance b : a 3. Qed.
Instance c : a 4. Qed.

Elpi AddAllClasses.
Elpi AddAllInstances.

Goal a 4. apply _. Qed.
