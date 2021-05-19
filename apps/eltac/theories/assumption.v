From elpi Require Export elpi.

Elpi Tactic assumption.
Elpi Accumulate lp:{{

  solve (goal Ctx Ev _ _ _) [] :-
    std.exists Ctx (x\ x = decl Ev _ _ ; x = def Ev _ _ _).

  solve _ _ :- coq.ltac.fail _ "No assumption unifies with the goal".

}}.

Elpi Typecheck.

Tactic Notation "eltac.assumption" := elpi assumption.
