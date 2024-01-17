Declare ML Module "coq-elpi-cs.plugin".
From elpi Require Import elpi.

Elpi Db cs.db lp:{{

  % predicate [canonical-solution Ctx Lhs Rhs] used to unify Lhs with Rhs, with
% - [Ctx] is the context
% - [Lhs] and [Rhs] are the terms to unify
:index (0 6 6)
pred canonical-solution i:goal-ctx, o:term, o:term.

}}.



Elpi Tactic canonical_solution.
Elpi Accumulate lp:{{

solve (goal Ctx _ {{ @eq lp:T lp:Lhs lp:Rhs }} _P []) _ :-
  canonical-solution Ctx Lhs Rhs,
  % std.assert! (P = {{ eq_refl lp:Lhs }}) "canonical-solution wrong solution".
  true.

}}.
Elpi Accumulate Db cs.db.
Elpi Typecheck.
Elpi CSFallbackTactic canonical_solution.
