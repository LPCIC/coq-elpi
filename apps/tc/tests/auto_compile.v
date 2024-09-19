From elpi.apps Require Import tc.

Elpi TC Solver Override TC.Solver All.

Require Import Bool.

(* TODO: How to add the #[deterministic] pragma in front of the class? *)
(* #[deterministic] Class A (T : Type) := {succ : T -> T}. *)
Class A (T : Type) := {succ : T -> T}.
#[local] Instance B : A nat := {succ n := S n}.
Instance C : A bool := {succ b := negb b}.
Instance Prod (X Y: Type) `(A X, A Y) : A (X * Y) := 
  {succ b := match b with (a, b) => (succ a, succ b) end}.

Elpi Accumulate TC.Solver lp:{{
  :after "firstHook"
  solve _ _ :- coq.say "Solving in ELPI!", fail.
}}.

Goal A (nat * (nat * bool)). apply _. Qed.

Module M.
  Class B (T : nat).
  Section A. 
    Instance X : B 1. Qed.
    Goal B 1. apply _. Qed.

    Global Instance Y : B 2. Qed.
    Goal B 2. apply _. Qed.
  End A.
  Goal B 1. Proof. Fail apply _. Abort.
  Goal B 2. Proof. apply _. Qed.

  Section B.
    Variable V : nat.
    Global Instance Z : `(B 0) -> B V. Qed.
    Global Instance W : B 0. Qed.
  End B.

  Goal B 0. apply _. Qed.
  Goal B 10. apply _. Qed.
End M.

Goal M.B 1. apply M.X. Qed.
Goal M.B 0. apply _. Qed.
Goal M.B 10. apply _. Qed.

Elpi Query TC.Solver lp:{{
  % Small test for instance order
  sigma I L\
  std.findall (tc.instance _ _ _ _) I,
  std.map-filter I (x\y\ x = tc.instance _ y {{:gref M.B}} _) 
    [{{:gref M.W}}, {{:gref M.Y}}, {{:gref M.Z}}].
}}.

Module S.
  Class Cl (i: nat).
  #[local] Instance Cl1 : Cl 1. Qed.
  #[global] Instance Cl2 : Cl 2. Qed.
  #[export] Instance Cl3 : Cl 3. Qed.
End S.

Elpi TC Solver Override TC.Solver None.
Goal S.Cl 1 /\ S.Cl 2 /\ S.Cl 3.
Proof. 
  split. all:cycle 1.
  split.
  apply _.
  Fail apply _.
  Import S.
  apply _.
  Fail apply _.
Abort.