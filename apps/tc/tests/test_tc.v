From elpi.apps Require Import tc.

Class a (N: nat).
Instance b : a 3. Qed.
Instance c : a 4. Qed.

TC.AddAllClasses.
TC.AddAllInstances.

Goal a 4. apply _. Qed.
