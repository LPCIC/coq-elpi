From elpi Require Export elpi.

Elpi Tactic assumption.
Elpi Accumulate lp:{{

  solve _ [goal Ctx Ev _ _ _] [] :-
    std.exists Ctx (x\ x = decl Ev _ _ ; x = def Ev _ _ _).

  solve _ _ _ :- coq.ltac1.fail _ "No assumption unifies with the goal".

}}.

Elpi Typecheck.

Tactic Notation "eltac.assumption" := elpi assumption.
