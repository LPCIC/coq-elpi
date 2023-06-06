From elpi.apps Require Import compiler.
From Coq Require Export Morphisms.

Global Instance pairSort: Params (@pair) 2 := {}.

Definition fst1 T := @fst T T .

Global Instance fstSort: Params (@fst1) 2 := {}.
Elpi AddInstances pairSort fstSort.
Elpi Print TC_solver.
