
From elpi.apps Require Import tc.
From elpi.apps Require Import eqSimplDef.

Elpi Debug "simple-compiler".
 
Set AddModes.

Elpi Override TC TC_solver Only Eqb.
Elpi AddClasses Eqb.
Elpi AddInstances Eqb.
Elpi Override TC TC_solver All.
Fail Check (fun n m : _ => eqb n m).

Elpi Trace Browser.
Goal (tt, (tt, true)) == (tt, (tt, true)) = true.
  easy.
Qed.

