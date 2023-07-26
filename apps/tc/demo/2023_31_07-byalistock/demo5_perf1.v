From elpi.apps.tc.tests Require Import stdppInj.
Elpi TC_solver. Set TimeRefine. Set TimeTC. Set Debug "elpitime". 

Goal Inj eq eq((compose (compose (compose f f)(compose f f))(compose (compose f f)(compose f f)))). Time apply _. Qed.