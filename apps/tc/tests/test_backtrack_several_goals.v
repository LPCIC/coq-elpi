Module M.
  Class C (i: nat).
  Instance i1: C 1 := {}.
  Instance i2: C 2 := {}.
  Class E (i: nat).
  Instance e1 : E 1 := {}.

  Lemma m {i} {H : C i} {H1 : E i}: C i. Admitted.

  Class D (i:nat) (o: C i).
  Instance d1 (H: C 1) : D 1 H := {}.

  Goal exists i, C i.
    eexists.
    Set Typeclasses Debug.
    (* Here backtracking is done *)
    apply m.
  Qed.
End M.

Module M1.
  Class C (i: nat).
  Instance i1: C 1 := {}.
  Instance i2: C 2 := {}.
  Class E (i: nat).
  Instance e1 : E 1 := {}.

  Lemma m {i} (H : C i) (H1 : E i): C i. Admitted.

  Class D (i:nat) (o: C i).
  Instance d1 (H: C 1) : D 1 H := {}.

  Goal exists i, C i.
    eexists.
    Set Typeclasses Debug.
    apply m.
    (* 
      Note: in coq the following command fails since apply is a single entry
      command, i.e. it cannot receive multiple goal at the same time.
      Therefore `apply _` will be triggered on the `n` goals. 
    *)
    Fail all: apply _.
    all: typeclasses eauto.
  Qed.
End M1.

(* Here similar problems using the coq-elpi solver *)
From elpi Require Import elpi tc.

Module ElpiBt.
  Class C (i: nat).
  Instance i1: C 1 := {}.
  Instance i2: C 2 := {}.
  Class E (i: nat).
  Instance e1 : E 1 := {}.

  Elpi Tactic T.

  Elpi Accumulate lp:{{
    msolve A B :- coq.say A, coq.ltac.all (coq.ltac.open solve-aux) A B.

    pred solve-aux i:goal, o:list sealed-goal.
    solve-aux (goal _ _ G _ _ as GG) L :-
      coq.say "Goal is" {coq.term->string G},
      solvee G S,
      coq.say "Solution for" {coq.term->string G} "is" {coq.term->string S},
      refine S GG L.

    pred solvee o:term, o:term.
    solvee {{C 2}} {{i2}}.
    solvee {{C 1}} {{i1}}.
    solvee {{E 1}} {{e1}}. 
  }}.
  

  Goal exists i, C i /\ E i.
    eexists.
    split.
    all : elpi T.
  Qed.
End ElpiBt.

Module M_in_elpi.
  Class C (i: nat).
  Instance c0: C 0 := {}.
  Instance c1: C 1 := {}.
  Class E (i: nat).
  Instance e0 : E 0 := {}.

  Lemma m {i} {H : C i} {H1 : E i}: C i. Admitted.

  Goal exists i, C i.
    eexists.
    apply m.
  Qed.
End M_in_elpi.