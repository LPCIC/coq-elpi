From elpi.apps Require Export derive.projK derive.bcongr.

(** A tactic pushing an equation under a constructor *)

Elpi Tactic injection.
Elpi Accumulate Db derive.projK.db.
Elpi Accumulate File "../derive/elpi/injection.elpi".
Elpi Accumulate lp:{{
  solve (goal _ _ _ _ [trm E] as G) NG :- !,
    of E Eq ER, !, ltac.injection ER Eq _ P,
    if (P = []) (coq.error "Could not generate new equations")
       (refine (app[New_|P]) G NG).

  solve _ _ :- usage.

  usage :- coq.error "Usage: eltac.injection <equation>".
}}.
Elpi Typecheck.

Tactic Notation "eltac.injection" constr(T) := elpi injection (T).