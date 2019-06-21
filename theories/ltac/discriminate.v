From elpi Require Export derive.isK.

(** A tactic proving the current goal out of a false equation *)

Elpi Tactic discriminate.
Elpi Accumulate Db derive.isK.db.
Elpi Accumulate File "ltac/discriminate.elpi".
Elpi Accumulate lp:{{
  solve [trm E] [goal Ctx Ev Ty _] [] :- !,
    Ctx => (of E Eq ER, !, ltac.discriminate ER Eq Ty Ev).

  solve _ _ _ :- usage.

  usage :- coq.error "Usage: discriminate <equation>".
}}.
Elpi Typecheck.
