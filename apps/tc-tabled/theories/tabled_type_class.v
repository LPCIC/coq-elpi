From elpi Require Import elpi.
From elpi.apps Require Import tc.

Elpi Tactic TC.TabledSolver.
Elpi TC Solver Register TC.TabledSolver.

Declare ML Module "rocq-elpi.tc-tabled".

From elpi.apps.tc_tabled.elpi Extra Dependency "tabled_type_class.elpi" as TabledTC.
Elpi Accumulate File TabledTC.

Elpi Export TC.TabledSolver.
