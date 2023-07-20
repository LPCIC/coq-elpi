From elpi.apps.tc.tests.importOrder Require Export f1.

Global Instance f2ba : A nat := {f x := x}.
Global Instance f2bb : A nat := {f x := x}.
Global Instance f2bc : A nat := {f x := x}.
Global Instance f2bd : A nat := {f x := x}.

Elpi AddInstances A.
(* Elpi SameOrderImport. *)
