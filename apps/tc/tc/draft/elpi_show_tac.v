From elpi Require Import elpi.

Elpi Tactic show.
Elpi Accumulate lp:{{

  solve (goal Ctx _Trigger Type Proof _) _ :-
    coq.say "Goal:" Ctx "\nProof:" Proof "\nType:" Type.

}}.
Elpi Typecheck.

Lemma tutorial x y  : x + 1 = y.
elpi show.
Abort.