From elpi Require Import compiler.

Module A.
  From Coq Require Import PeanoNat.

  Class Succ (F : nat -> nat).
  Global Instance SuccNat : Succ S := {}.

  (* Here we are in Coq *)
  Check (_ : Succ PeanoNat.Nat.succ).
  Check (_ : Succ S).

  Elpi Override TC TC_check All.
  Elpi AddInstances Succ.

  (* Here we are in Elpi *)
  Check (_ : Succ PeanoNat.Nat.succ).
  Check (_ : Succ S).

  Elpi Accumulate TC_check lp:{{
    tc {{:gref Succ}} {{Succ PeanoNat.Nat.succ}} Sol :-
      tc {{:gref Succ}} {{Succ S}} Sol.
  }}.

  Check (_ : Succ PeanoNat.Nat.succ).
  Check (_ : Succ S).
End A.

Module B.
  From Coq.Program Require Export Basics.
  From Coq Require Export Setoid.

  Set Implicit Arguments.

  Class Inj {A B} (R : relation A) (S : relation B) (f : A -> B) : Prop :=
    inj x y : S (f x) (f y) -> R x y.

  Global Instance compose_inj {A B C} R1 R2 R3 (f : A -> B) (g : B -> C) :
  Inj R1 R2 f -> Inj R2 R3 g -> Inj R1 R3 (compose g f).
  Proof.
    unfold Inj, compose.
    intros.
    apply H, H0.
    easy.
  Qed.

  Definition times2 x := x * 2.

  From Coq Require Import Lia.

  Elpi AddAllInstances.
  Global Instance times2_inj: Inj eq eq (times2).
  Proof.
    unfold times2, Inj; intros. lia.
  Qed.

  Elpi Override TC TC_check None.

  Check (_ : Inj eq eq times2).
  Check (_: Inj eq eq (fun x => x * 2)).

  Elpi Override TC TC_check All.
  Elpi AddAllInstances.

  Check (_ : Inj eq eq times2).
  Check (_: Inj eq eq (fun x => x * 2)).

  Elpi Accumulate TC_check lp:{{
    :name "rename1"
    tc {{:gref Inj}} {{Inj lp:A lp:B lp:F}} Sol :-
      F = {{fun x => x * 2}},
      coq.say "Found unfold of times2 !",
      tc {{:gref Inj}} {{Inj lp:A lp:B times2}} Sol.
  }}.
  Check (_: Inj eq eq (fun x => x * 2)).

  Elpi Accumulate TC_check lp:{{
    pred alias i:term, o:term.
    alias {{fun x => x * 2}} {{times2}}.
  }}.

  Elpi Accumulate TC_check lp:{{
    :before "rename1"
    tc {{:gref Inj}} {{Inj lp:A lp:B lp:F}} Sol :-
      alias F F',
      coq.say "Found unfold of times2 with alias !",
      tc {{:gref Inj}} {{Inj lp:A lp:B lp:F'}} Sol.
  }}.
  Elpi Typecheck TC_check.

  Check (_: Inj eq eq (fun x => x * 2)).

End B.
