From elpi.apps.tc.tests.importOrder Require Export f1.
From elpi.apps.tc.tests.importOrder Require Export sameOrderCommand.


Global Instance f2aa : A nat := {f x := x}.
Global Instance f2ab : A nat := {f x := x}.
Global Instance f2ac : A nat := {f x := x}.
Global Instance f2ad : A nat := {f x := x}.

Elpi AddInstances A.
Elpi SameOrderImport.