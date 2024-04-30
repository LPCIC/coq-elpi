From elpi.apps.tc.tests Require Import stdppInj.
Set TC Time Refine. Set TC Time Instance Search. Set Debug "elpitime".
Goal Inj eq eq((compose f f )). Time apply _. Qed.
