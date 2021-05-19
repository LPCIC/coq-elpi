From elpi Require Export elpi.

Elpi Tactic fail.
Elpi Accumulate lp:{{
  solve (goal _ _ _ _ [int N]) _ :- coq.ltac.fail N.
  solve (goal _ _ _ _ Args) _ :- coq.error "eltac.fail expects 1 integer, you passed:" Args.

}}.
Elpi Typecheck.

Tactic Notation "eltac.fail" int(n) := elpi fail ltac_int:(n).
