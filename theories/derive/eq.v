Require Import Bool.
Require Import elpi.

Elpi Command derive.eq.
Elpi Accumulate File "derive/eq.elpi".
Elpi Accumulate "
  main [str I] :- !,
    coq-locate I T,
    if (T = indt GR) (derive-eq GR) usage.
  main _ :- usage.

  usage :- coq-error ""Usage: derive.eq <inductive type name>"".
". 
Elpi Typecheck.

