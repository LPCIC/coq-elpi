From elpi Require Import elpi.

(** derive.isK generates a function per constructor that returns
    true iff it is applied to such constructor *)

Elpi Command derive.isK.
Elpi Accumulate File "derive/isK.elpi".
Elpi Accumulate "
  main [str I] :- !,
    coq-locate I T,
    if (T = indt GR) (derive-isK GR) usage.
  main _ :- usage.

  usage :- coq-error ""Usage: derive.isK <inductive type name>"".
".
Elpi Typecheck.
