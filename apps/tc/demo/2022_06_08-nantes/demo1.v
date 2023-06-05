From elpi Require Import compiler.
From Coq.Program Require Export Basics.
From Coq Require Export Setoid.
From Coq Require Import Lia.
From Coq Require Import PeanoNat.

Elpi Debug "simple-compiler".

Module A.

  Class Succ (F : nat -> nat).
  Global Instance SuccNat : Succ S := {}.

  (* Here we are in Coq *)
  Check (_ : Succ PeanoNat.Nat.succ).
  Check (_ : Succ S).

  (* Here we are in Elpi *)
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

(* We come back to coq *)
Elpi Override TC TC_check None.

Module B.
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

  Global Instance times2_inj: Inj eq eq (times2).
  Proof. red; unfold times2; lia. Qed.

  (* Here we are in coq *)
  Check (_ : Inj eq eq times2).
  Check (_: Inj eq eq (fun x => x * 2)).

  (* Here we are in elpi *)
  Elpi Override TC TC_check All.
  Elpi AddInstances Inj.

  Check (_ : Inj eq eq times2).

  (* Elpi Trace Browser. *)
  Check (_: Inj eq eq (fun x => x * 2)).

  Module UseAlias1.
    Elpi Accumulate TC_check lp:{{
      :name "rename1"
      tc {{:gref Inj}} {{Inj lp:A lp:B lp:F}} Sol :-
        F = {{fun x => x * 2}},
        coq.say "Found unfold of times2 !",
        tc {{:gref Inj}} {{Inj lp:A lp:B times2}} Sol.
    }}.
    Check (_: Inj eq eq (fun x => x * 2)).
  End UseAlias1.
  
  Module UseAlias2.
    Elpi Accumulate TC_check lp:{{
      :before "rename1"
      :name "rename2"
      tc {{:gref Inj}} {{Inj lp:A lp:B lp:F}} Sol :-
        coq.unify-eq F {{times2}} ok,
        coq.say "Found unfold of times2 !",
        tc {{:gref Inj}} {{Inj lp:A lp:B times2}} Sol.
    }}.
    Check (_: Inj eq eq (fun x => x * 2)).
  End UseAlias2.

  Module UseAlias3.
    Elpi Accumulate TC_check lp:{{
      pred alias i:term, o:term.
      alias {{fun x => x * 2}} {{times2}}.
    }}.

    (* Hand alias rule by hand  *)
    Elpi Accumulate TC_check lp:{{
      :before "rename2"
      :name "rename3"
      tc {{:gref Inj}} {{Inj lp:A lp:B lp:F}} Sol :-
        alias F F', 
        coq.say "Found unfold of times2 with alias !",
        tc {{:gref Inj}} {{Inj lp:A lp:B lp:F'}} Sol.
    }}.
    Check (_: Inj eq eq (fun y => y * 2)).
  End UseAlias3.

  Module UseAlias4.
    (* Trying to generalize *)
    Elpi Accumulate TC_check lp:{{
      pred replace-with-alias i:term, o:term.
      replace-with-alias A Sol :- alias A Sol.
      replace-with-alias (app ToReplace) (app Sol) :-
        std.map ToReplace replace-with-alias Sol.
      replace-with-alias (fun A T Bo) (fun A T' Bo') :-
        pi x\ 
          coq.say "Bo" Bo,
          replace-with-alias (Bo x) (Bo' x),
          replace-with-alias T T'.
      replace-with-alias A A.

      :before "rename3"
      :name "rename4"
      tc {{:gref Inj}} T Sol :- !,
        replace-with-alias T T',
        coq.say "Found unfold of times2 with alias2 !",
        tc {{:gref Inj}} T' Sol.
    }}.
    Check (_: Inj eq eq (fun y => y * 2)).
  End UseAlias4.
End B.
