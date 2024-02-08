Declare ML Module "coq-elpi-cs.plugin".
From elpi Require Import elpi.

Elpi Db cs.db lp:{{

  % predicate [canonical-solution Ctx Lhs Rhs] used to unify Lhs with Rhs, with
% - [Ctx] is the context
% - [Lhs] and [Rhs] are the terms to unify
:index (0 6 6)
pred cs i:goal-ctx, o:term, o:term.

}}.



Elpi Tactic canonical_solution.
Elpi Accumulate lp:{{

solve (goal Ctx _ _Ty Sol [trm Proj, trm Rhs]) _ :-
  cs Ctx Proj Rhs Sol,
  % std.assert! (P = {{ eq_refl lp:Lhs }}) "cs: wrong solution".
  true.

}}.
Elpi Accumulate Db cs.db.
Elpi Typecheck.
Elpi CSFallbackTactic canonical_solution.
