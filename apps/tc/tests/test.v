From elpi.apps.tc.tests Require Import stdppInj.
From Coq Require Import Setoid.
Elpi Debug "time-refine".
Set Debug "elpitime".

Goal Inj eq eq((compose (compose (compose f f )(compose f f ))(compose (compose f f )(compose f f )))). Time apply _. Qed.
