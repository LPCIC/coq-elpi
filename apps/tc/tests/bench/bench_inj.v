From elpi.apps.tc.tests Require Import stdppInj.
Set TC Time Refine. Set TC Time Instance Search. Set Debug "elpi".
Goal Inj eq eq((compose (compose (compose f f )(compose f f ))(compose (compose f f )(compose f f )))). Time apply _. Qed.
