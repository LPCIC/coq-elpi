Require Import Bool.
Require Import elpi.

Elpi Db derive.eq.db "type eq-db term -> term -> term -> prop.".

Elpi Command derive.eq.
Elpi Accumulate Db derive.eq.db.
Elpi Accumulate File "derive/eq.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, derive.eq.main I O _.
  main [str I] :- !, 
    coq.locate I T, term->gr T GR, coq.gr->id GR Id, O is Id ^ ""_eq"",
    derive.eq.main I O _.
  main _ :- usage.

  usage :- coq.error ""Usage: derive.eq <inductive type name> [<output name>]"".
".
Elpi Typecheck.

