From elpi.apps.tc.tests.importOrder Require Export f1.

Global Instance f3a : A nat := {f x := x}.
Global Instance f3b : A nat := {f x := x}.
Global Instance f3c : A nat := {f x := x}.
Elpi AddAllInstances.
Elpi SameOrderImport.

Section S1.
  Global Instance f3d : A nat := {f x := x}.
  Global Instance f3e : A nat := {f x := x}.
  Global Instance f3f : A nat := {f x := x}.
  Elpi AddAllInstances.
  Elpi SameOrderImport.
MySectionEnd.
Elpi SameOrderImport.

Section S2.
  Context (T : Set).
  Global Instance f3g : A T := {f x := x}.
  Elpi AddAllInstances.
  Elpi SameOrderImport.
MySectionEnd.
Elpi SameOrderImport.

Section S3.
  Context (T : Set).
  Global Instance f3g2 : A (T: Set) := {f x := x}.

  Global Instance f3h T1 T2 `(A T1, A T2) : A (T1 * T2) := {f x := x}.

  Global Instance f3g3 : A (T: Set) := {f x := x}.
  Global Instance f3g4 : A (T: Set) | 10 := {f x := x}.

  Elpi AddAllInstances.
  Elpi SameOrderImport.
MySectionEnd.

Elpi SameOrderImport.