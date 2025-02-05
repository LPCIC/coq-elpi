From elpi_apps_tc_tests_stdlib Require Import stdppInj.
Elpi TC.Solver. Set TC Time Refine. Set TC Time Instance Search. Set Debug "elpitime".
Goal Inj eq eq((compose f f )). Time apply _. Qed.
