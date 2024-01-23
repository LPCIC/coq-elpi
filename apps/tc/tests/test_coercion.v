From elpi Require Import tc.

Module Animals.

  Module Bird1.
    Inductive info := Fly | NotFly.

    Class Animal (i : info).
    
    Class Bird (i : info) := IsAnimal :> Animal i.

    Instance dove : Bird Fly. split. Qed.

    (* It exists a ground solution for tc-Animal *)
    Elpi Query TC.Solver lp:{{
      tc-elpi.apps.tc.tests.test_coercion.Animals.Bird1.tc-Animal _ S, ground_term S.
    }}.

    (* It does not exist a solution for tc-Animal with a flexible solution *)
    Elpi Query TC.Solver lp:{{
      not (tc-elpi.apps.tc.tests.test_coercion.Animals.Bird1.tc-Animal _ S, not (ground_term S)).
    }}.

    Goal Animal Fly. apply _. Qed.
    Goal Animal NotFly. Fail solve [apply _]. Abort.

  End Bird1.

  Module Bird2.

    Class Animal.

    Class Bird1 := IsAnimal : Animal.

    Instance dove : Bird1. split. Qed.

    (* It does not exists an instance for Animal1 *)
    Elpi Query TC.Solver lp:{{
      not (tc-elpi.apps.tc.tests.test_coercion.Animals.Bird2.tc-Animal _).
    }}.

    Goal Animal. Fail solve [apply _]. apply IsAnimal. Abort.

  End Bird2.

End Animals.

Module Vehicle.

  Class Wheels (i: nat).

  Class Boat.

  Class NoWheels `{Wheels 0} := {
    (* the first argument of no_wheels is implicit! *)
    no_wheels : Boat;
  }.

  Arguments no_wheels {_}.

  Instance f `{H : Wheels 0} : NoWheels. Admitted.

  Goal Wheels 0 -> Boat.
    intros.
    apply no_wheels.
    apply _.
  Qed.

End Vehicle.
