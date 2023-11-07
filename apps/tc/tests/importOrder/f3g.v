From elpi.apps.tc.tests.importOrder Require Export f1.

Module M8.
  Class Classe (A: Type) (B: Type).

  Global Instance I (a b c d: Type): Classe a a -> Classe b c. Admitted.

  Elpi SameOrderImport.
End M8.
