From elpi Require Export derive.projK.

(** A tactic pushing an equation under a constructor *)

Elpi Tactic injection.
Elpi Accumulate File "ltac/injection.elpi".
Elpi Accumulate "
  solve [trm E] [goal Ctx Ev Ty _ as G] NG :- !,
    Ctx => (of E Eq ER, !, injection ER Eq L P),
    refine (app[hole|P]) G NG,
    print_constraints.

  solve _ _ _ :- usage.

  usage :- coq-error ""Usage: injection <equation>"".
".
Elpi Typecheck.
