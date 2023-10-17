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
  main [str A] :- 
    coq.locate A GR,
    % coq.say {attributes},
    coq.say "Adding :" GR,
    if (coq.TC.class? GR) (add-class-gr classic GR)
       (add-inst->db [] ff GR).
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


