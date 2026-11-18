From elpi Require Import elpi.

(* coq.ltac.name-uvar, coq.ltac.name-goal, coq.ltac.name-sealed-goal,
   coq.ltac.goal-name-free?, coq.ltac.fresh-goal-name,
   coq.ltac.goal-name->sealed-goal, coq.ltac.goal-name->goal *)

Elpi Command q.

Elpi Query lp:{{
  coq.ltac.goal-name-free? "q",
  coq.typecheck X {{ nat }} ok, % X is linked to a Rocq evar
  coq.ltac.name-uvar X "q",
  std.assert! (not (coq.ltac.goal-name-free? "q")) "name taken",
  coq.ltac.name-uvar X "q", % same name, same evar: ok
  coq.typecheck Z {{ nat }} ok,
  std.assert! (not (coq.ltac.name-uvar Z "q")) "name taken by another evar",
  coq.ltac.goal-name->sealed-goal "q" G,
  std.assert! (G = seal (goal [] _ _ Y _), same_var X Y) "goal-name->sealed-goal",
  coq.ltac.goal-name->goal "q" G1,
  std.assert! (G1 = goal [] _ _ Y1 _, same_var X Y1) "goal-name->goal",
  std.assert! (not (coq.ltac.goal-name->goal "nope" _)) "no such goal",
  std.assert! (not (coq.ltac.goal-name->sealed-goal "nope" _)) "no such goal"
}}.

Elpi Query lp:{{
  coq.typecheck P {{ nat }} ok,
  coq.ltac.name-uvar P "p",
  coq.ltac.fresh-goal-name "p" P1,
  std.assert! (P1 = "p0") "fresh",
  coq.ltac.fresh-goal-name "d" D,
  std.assert! (D = "d") "fresh"
}}.

Fail Elpi Query lp:{{ coq.ltac.name-uvar {{ 0 }} "z" }}.
(* not linked to a Rocq evar *)
Fail Elpi Query lp:{{ coq.ltac.name-uvar _ "z" }}.

(* the name of an evar is visible to Rocq after the tactic *)
Elpi Tactic name.
Elpi Accumulate lp:{{
solve (goal _ _ {{ lp:A = _ }} _ [str N]) _ :-
  coq.ltac.name-uvar A N.
}}.

Goal exists n : nat, n = n.
eexists.
elpi name "foo".
instantiate (foo := 3).
reflexivity.
Qed.

(* the name of a goal is visible to Rocq after the tactic *)
Elpi Tactic name_goal.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ [str N] as G) [seal G] :-
  coq.ltac.name-goal G N.
}}.

Goal True.
elpi name_goal "g".
[g]: exact I.
Qed.

Elpi Tactic split_named.
Elpi Accumulate lp:{{
solve G GL :-
  refine {{ conj _ _ }} G GL,
  GL = [G1, G2],
  coq.ltac.name-sealed-goal G1 "left",
  coq.ltac.name-sealed-goal G2 "right".
}}.

Goal forall n : nat, n = n /\ True.
intro n.
elpi split_named.
[right]: exact I.
[left]: reflexivity.
Qed.

(* names given by Rocq are visible to Elpi *)
Elpi Tactic get.
Elpi Accumulate lp:{{
solve (goal _ _ {{ lp:A = _ }} _ [str N]) _ :-
  coq.ltac.goal-name->goal N (goal _ _ _ E _),
  std.assert! (same_term E A) "goal-name->goal",
  coq.ltac.goal-name->sealed-goal N SG,
  coq.ltac.open (g\ gl\ sigma E1\ g = goal _ _ _ E1 _, coq.say E1, gl = []) SG _.
}}.

Goal exists n : nat, n = n.
refine (ex_intro _ ?[bar] _).
elpi get "bar".
Abort.

Goal forall m : nat, exists n : nat, n = m.
intro m.
refine (ex_intro _ ?[baz] _).
elpi get "baz".
Abort.

(* a goal living in a different context *)
Elpi Tactic get_other.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ [str N]) _ :-
  coq.ltac.goal-name->sealed-goal N (nabla _).
}}.
Elpi Tactic get_other_simple.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ [str N]) _ :-
  coq.ltac.goal-name->goal N _.
}}.

Goal True /\ (forall m : nat, m = m).
split.
2: intro m; refine (eq_trans ?[other] _).
1: elpi get_other "other".
Fail elpi get_other_simple "other".
Abort.
