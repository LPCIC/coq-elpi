From elpi Require Import tc.

Set TC NameShortPath.

Module Animals.

  Class Animal.

  Class Bird := IsAnimal :> Animal.
  Instance dove : Bird. split. Qed.

  Elpi Query TC.Solver lp:{{
    tc-Animal S, ground_term S.
  }}.

  Goal Animal. apply _. Qed.

End Animals.