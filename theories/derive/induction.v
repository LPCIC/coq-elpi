From elpi Require Import elpi derive.param1 derive.param1P.

Elpi Db derive.induction.db "
  type induction-db term -> term -> prop.
".

Elpi Command derive.induction.
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1P.db.
Elpi Accumulate Db derive.induction.db.
Elpi Accumulate File "derive/induction.elpi".
Elpi Accumulate "
  main [str I, str O] :- !,
    coq-locate I T, if (T = indt GR) (derive-induction GR O) usage.
  main [str I] :- !,
    if (coq-locate I (indt GR))
       (main [str I, str {calc ({coq-gr->id GR} ^ ""_induction"")}])
       usage.
  main _ :- usage.

  usage :- coq-error ""Usage: derive.induction <inductive type name> [<output name>]"".
".  
Elpi Typecheck.

