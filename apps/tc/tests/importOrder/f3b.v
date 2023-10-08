From elpi.apps.tc.tests.importOrder Require Import f2b.
From elpi.apps.tc.tests.importOrder Require Import f2a.
(* Elpi AddAllInstances. *)
Print HintDb typeclass_instances.

Elpi Print TC_solver "tests/f3b".
Elpi SameOrderImport.