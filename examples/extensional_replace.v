Require Import Arith List FunctionalExtensionality.
From elpi Require Import elpi.

Lemma ring_example x : x + 1 = 1 + x.
Proof. ring. Qed.

Goal forall l, map (fun x => x + 1) l = map (fun x => 1 + x) l.
Proof.
Fail replace (x + 1) with (1 + x) by ring.
replace (fun x => x + 1) with (fun x => 1 + x).
  easy.
extensionality x.
ring.
Qed.

Elpi Tactic show.
Elpi Accumulate lp:{{

  pred process i:list argument, o:string.

  process [open-trm K_ T] S :-
      coq.term->string T S.

  process [trm T] S :-
      coq.term->string T S.
  
  solve (goal Ctx _Trigger Type Proof Args) _ :-
    % process Args Txt,
    coq.say "Goal:" Ctx "|-" Proof ":" Type ">->" Args.

}}.

Elpi Typecheck.

Ltac prove_by_extensionality_and_ring term1 term2 :=
  replace term1 with term2;[ |
    let Var_name := fresh "mame_for_bound_variable" in
      extensionality Var_name; ring
  ].

Elpi Tactic replace.

Elpi Accumulate lp:{{
  pred process i:argument, i:argument, i:term, o:term, o:term.

% The header says we want to replace a formula with one unknown
% by a formula with also one unknown in the Goal.
  process (open-trm 1 (fun Name _Ty F1))    % to be replaced
          (open-trm 1 (fun _Name1 _Ty1 F2)) % to be inserted in place
          GoalConcl                         % term in which to replace
          FirstLambda                       % Lambda to replace
          (fun Name2 Ty2 H'):-              % lambda to insert in place

% The 1 in first and second arguments expresses there is exactly one
% unknown in these terms (expected to be the same unknown, not checked here
% We expect the unknown to be instantiated by a bound variable in
% the first lambda in the goal.  We perform the replacement in that lambda
% without checking that there is progress (in this preliminary version).

% We look for lambdas in the goal.  Behware that
% TopLambdas contains the expressions in reverse order of their
% discovery in a left-to-right traversal.
%  std.do! [
    ((pi T A T\ fold-map T A T [T | A] :- T = (fun _ _ _)) =>
      fold-map GoalConcl [] _ TopLambdas),
    MSG is "variable " ^ {coq.name->id Name} ^ " is unknown",
% We take the first lambda
    std.assert! ({std.rev TopLambdas} = [FirstLambda | _]) MSG,
    FirstLambda = (fun Name2 Ty2 H),
% We perform the required replacement in the body of the lambda
    (pi C \ copy (F1 C) (F2 C) => copy (H C) (H' C))
  %]
  .

solve (goal _ _ Type _ [Arg1, Arg2] as G) GL :-
    process Arg1 Arg2 Type Term1 Term2,
    std.assert! (coq.ltac.call "prove_by_extensionality_and_ring"
        [trm Term1, trm Term2] G GL) "ltac call failed".
}}.

Elpi Typecheck.

Goal forall l, map (fun x => (x + 1) + 2) l = map (fun x => (1 + x) + 2) l.
Proof.
now intros l; elpi replace (x + 1) (1 + x).
Qed.
