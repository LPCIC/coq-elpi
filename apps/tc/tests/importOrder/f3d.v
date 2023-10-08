From elpi.apps.tc.tests.importOrder Require Export f1.
From elpi.apps.tc.tests.importOrder Require Import f2b.
Elpi SameOrderImport.

Global Instance f3a' T1 T2 `(A T1, A T2) : A (T1 * T2) := {f x := x}.
Elpi AddInstances A.

Elpi SameOrderImport.
Module M4'.
  (* From elpi.apps.tc.tests.importOrder Require Import f2a. *)
  Elpi SameOrderImport.

  Global Instance f3a : A nat := {f x := x}.
  Elpi AddInstances f3a.

  Section S1.
    Global Instance f3b : A nat := {f x := x}.
    Elpi AddInstances f3b.
    Section S1'.
      Global Instance f3c : A nat := {f x := x}.
      Elpi AddInstances f3c.
    MySectionEnd.
  MySectionEnd.

  Elpi SameOrderImport.

  Section S2.
    Global Instance f3h T1 T2 `(A T1, A T2) : A (T1 * T2) := {f x := x}.
    Elpi AddInstances f3h.
  MySectionEnd.
End M4'.