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
  main [str I, str O] :- !, derive.induction.main I O _.
  main [str I] :- !,
    coq.locate I T, term->gr T GR, Name is {coq.gr->id GR} ^ ""_induction"",
    derive.induction.main I Name _.
  main _ :- usage.

  usage :- coq.error ""Usage: derive.induction <inductive type name> [<output suffix>]"".
".  
Elpi Typecheck.

