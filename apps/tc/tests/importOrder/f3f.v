From elpi.apps.tc.tests.importOrder Require Import f1.

Section S1.
  Context (T : Set).
  Global Instance f3a : A T := {f x := x}.
  Elpi AddInstances f3a.
  Elpi SameOrderImport.

  Section S2.
    Context (T1 : Set).
    Global Instance f3b : A T1 := {f x := x}.
    Elpi AddInstances f3b.
  MySectionEnd.
  
  Elpi SameOrderImport.
MySectionEnd.
Elpi SameOrderImport.