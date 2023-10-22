From elpi.apps.tc.tests.importOrder Require Export f1.
From elpi.apps.tc.tests.importOrder Require Import f2b.
From elpi.apps.tc.tests.importOrder Require Import f2a.

Global Instance f3a' T1 T2 `(A T1, A T2) : A (T1 * T2) := {f x := x}.

Elpi SameOrderImport.
Module M4'.
  Global Instance f3a : A nat := {f x := x}.

  Section S1.
    Global Instance f3b : A nat := {f x := x}.
    Section S1'.
      Global Instance f3c : A nat := {f x := x}.
    End S1'.
  End S1.

  Section S2.
    Global Instance f3h T1 T2 `(A T1, A T2) : A (T1 * T2) | 100 := {f x := x}.
  End S2.
End M4'.


Elpi SameOrderImport.