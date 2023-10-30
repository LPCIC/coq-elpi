From elpi.apps.tc.tests.importOrder Require Import f1.

Section S1.
  Context (T : Set).
  Global Instance f3a : A T := {f x := x}.
  
  Elpi SameOrderImport.

  Section S2.
    Context (T1 : Set).
    Global Instance f3b : A T1 := {f x := x}.
    
  End S2.
  
  Elpi SameOrderImport.
End S1.
Elpi SameOrderImport.