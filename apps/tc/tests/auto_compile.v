From elpi.apps Require Import tc.

From elpi.apps.tc Extra Dependency "base.elpi" as base.
From elpi.apps.tc Extra Dependency "compiler.elpi" as compiler.
From elpi.apps.tc Extra Dependency "tc_aux.elpi" as tc_aux.
From elpi.apps.tc Extra Dependency "create_tc_predicate.elpi" as create_tc_predicate.

Elpi Command add_instance.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate Db tc.db.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate File compiler.
Elpi Accumulate lp:{{
  main [trm (global Inst), trm (global TC), str Locality, int Prio] :- 
    add-inst Inst TC Locality Prio.

  main [trm (global GR)] :- 
    add-class-gr classic GR.
}}.
Elpi Typecheck.
Elpi Override Register add_instance.
Elpi Override TC TC_solver All.

Require Import Bool.

(* TODO: How to add the #[deterministic] pragma in front of the class? *)
(* #[deterministic] Class A (T : Type) := {succ : T -> T}. *)
Class A (T : Type) := {succ : T -> T}.
#[local] Instance B : A nat := {succ n := S n}.
Instance C : A bool := {succ b := negb b}.
Instance Prod (X Y: Type) `(A X, A Y) : A (X * Y) := 
  {succ b := match b with (a, b) => (succ a, succ b) end}.

Elpi Accumulate TC_solver lp:{{
  :after "firstHook"
  solve _ _ :- coq.say "Solving in ELPI!", fail.
}}.
Elpi Typecheck.

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

(* 
  TODO: @gares @FissoreD we have an unwanted warning:
  constant tc-elpi.apps.tc.tests.auto_compile.M.tc-B has no declared type
  since the considered instances come from a module.
*)
Elpi Query TC_solver lp:{{
  % Small test for instance order
  sigma I L\
  std.findall (instance _ _ _) I,
  std.map-filter I (x\y\ x = instance _ y {{:gref M.B}}) 
    [{{:gref M.W}}, {{:gref M.Y}}, {{:gref M.Z}}].
}}.