From elpi.apps Require Export derive.isK derive.bcongr derive.eqK.

(** A tactic proving the current goal out of a false equation *)

Elpi Tactic discriminate.
Elpi Accumulate Db derive.isK.db.
Elpi Accumulate File "../derive/elpi/discriminate.elpi".
Elpi Accumulate lp:{{
  solve [trm E] (goal _ Ev Ty _ _) [] :- !,
    of E Eq ER, !, ltac.discriminate ER Eq Ty Ev.

  solve _ _ _ :- usage.

  usage :- coq.error "Usage: eltac.discriminate <equation>".
}}.
Elpi Typecheck.

Tactic Notation "eltac.discriminate" constr(T) := elpi discriminate (T).
