From elpi Require Export elpi.

Elpi Tactic fail.
Elpi Accumulate lp:{{
  solve [int N] _ _ :- coq.ltac1.fail N.
  solve Args _ _ :- coq.error "eltac.fail expects 1 integer, you passed:" Args.

}}.
Elpi Typecheck.

Tactic Notation "eltac.fail" int(n) := elpi fail ltac_int:(n).
