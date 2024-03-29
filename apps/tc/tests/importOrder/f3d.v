From elpi.apps.tc.tests.importOrder Require Export f1.
From elpi.apps.tc.tests.importOrder Require Import f2b.
Elpi SameOrderImport.

Global Instance f3a' T1 T2 `(A T1, A T2) : A (T1 * T2) := {f x := x}.


Elpi SameOrderImport.
Module M4'.
  (* From elpi.apps.tc.tests.importOrder Require Import f2a. *)
  Elpi SameOrderImport.

  Global Instance f3a : A nat := {f x := x}.
  

  Section S1. Variable X : Type.
    Global Instance f3b : A nat := {f x := x}.
    
    Section S1'. Variable Y : Type.
      Global Instance f3c : A nat := {f x := x}.
      
    End S1'.
  End S1.

  Elpi SameOrderImport.

  Section S2. Variable X : Type.
    Global Instance f3h T1 T2 `(A T1, A T2) : A (T1 * T2) := {f x := x}.
  End S2.
End M4'.

Elpi SameOrderImport.
