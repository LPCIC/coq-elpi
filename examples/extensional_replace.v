Require Import Arith List FunctionalExtensionality.
From elpi Require Import elpi.

Lemma ring_example x : x + 1 = 1 + x.
Proof. ring. Qed.

Lemma fail_ring_under l : map (fun x => x + 1) l = map (fun x => 1 + x) l.
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

Lemma toto l : map (fun x => x + 1) l = map (fun x => 1 + x) l.
elpi show (fun x => x + y).
apply fail_ring_under.
Qed.

Elpi Tactic replace.

Elpi Accumulate lp:{{
  pred process i:argument, i:argument, i:term.

% The header says we want to replace a formula with one unknown
% by a formula with also one unknown in the Goal.
  process (open-trm 1 (fun Name _Ty F1))
          (open-trm 1 (fun _Name1 _Ty1 F2)) G :-
% We expect the unknown to be instantiated by a bound variable in
% the goal, so we look for lambdas in the goal.
    ((pi T A T\ fold-map T A T [T | A] :- T = (fun _ _ _)) =>
      fold-map G [] _ TopLambdas),
      MSG is "variable " ^ {coq.name->id Name} ^ " is unknown",!,
% We take the first lambda, and perform the modification in it.
      std.assert! (TopLambdas = [fun Name2 Ty2 H | _]) MSG,
      (pi C \ (copy (F1 C) (F2 C) => copy (H C) (H' C))),
      ((copy (fun Name2 Ty2 H) (fun Name2 Ty2 H')) =>
       copy G G'),
  %     coq.term->string (fun Name2 Ty2 H) Inp,
  %     coq.say Inp,
  %    coq.term->string  (fun Name2 Ty2 H') Res,
      coq.term->string G' Res,
      coq.say Res.

solve (goal _Ctx _Trigger Type _ [Arg1, Arg2]) _ :-
    process Arg1 Arg2 Type.
}}.

Elpi Typecheck.

Goal forall l, map (fun x => (x + 1) + 2) l = map (fun x => (1 + x) + 2) l.
Proof. intros l.
elpi replace (1 + x) (x + 1).