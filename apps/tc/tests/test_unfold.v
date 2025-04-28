From elpi Require Import tc.

Module NAT.
  (* Unfold on S vs Nat.succ *)
  TC.Unfold Nat.succ.
  Class nat2 (T : nat -> nat).

  Elpi Accumulate TC.Solver lp:{{
    % Just to print what is beeing normalized
    :after "firstHook"
    tc.normalize-ty T _ :- coq.say "Normalizing" T, fail, !.
  }}.

  (* The unfold is done in the goal *)
  Module NAT1.
    Instance i1 : nat2 S. Qed.
    Goal nat2 Nat.succ. apply _. Qed.
  End NAT1.

  (* The unfold is done at instance compilation *)
  Module NAT2.
    Instance i1 : nat2 Nat.succ. Qed.
    Goal nat2 S. apply _. Qed.
  End NAT2.

  (* The unfold is done on the instance and on the goal *)
  Module NAT3.
    Instance i1 : nat2 Nat.succ. Qed.
    Goal nat2 Nat.succ. apply _. Qed.
  End NAT3.
End NAT.