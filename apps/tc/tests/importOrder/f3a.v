From elpi.apps.tc.tests.importOrder Require Import f2a.
From elpi.apps.tc.tests.importOrder Require Import f2b.
(* Elpi AddAllInstances. *)
Print HintDb typeclass_instances.

Elpi Print TC_solver "tests/f3a".
Elpi SameOrderImport.
