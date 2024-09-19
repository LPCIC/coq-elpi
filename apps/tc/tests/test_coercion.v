From elpi Require Import tc.

Module Animals.

  Module Bird1.
    Inductive info := Fly | NotFly.

    Class Animal (i : info).
    
    Class Bird (i : info) := IsAnimal :: Animal i.

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

  Class NoWheels := {
    (* the first argument of no_wheels is implicit! *)
    wheels0 :: Wheels 0;
  }.

  Class Boat := {
    wheels :: NoWheels
  }.

  Goal Boat -> Wheels 0.
    intros.
    apply _.
  Qed.

End Vehicle.

Module foo.
  Class B (i : nat).

  Section s.
    (* Class with coercion depending on section parameters *)
    Context (A : Type).
    Class C (i : nat) : Set := {
      f (x : A) :: B i
    }.
  End s.
End foo.

Module foo1.
  Class B (i : nat).

  Section s.
    (* Class with coercion not depending on section parameters *)
    Class C (i : nat) : Set := {
      f :: B i
    }.
  End s.

  Goal C 3 -> B 3.
    apply _.
  Abort.
End foo1.

Module localCoercion.
  Class B (i : nat).
  Section s.
    Class C (i : nat) : Set := {
      #[local] f :: B i
    }.
    Goal C 3 -> B 3.
      apply _.
    Qed.
  End s.
  Goal C 3 -> B 3.
    Fail apply _.
  Abort.
End localCoercion.
