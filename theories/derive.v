From elpi Require Export derive.eq derive.isK.

Elpi Command derive.
Elpi Accumulate Db derive.eq.db.
Elpi Accumulate Db derive.isK.db.
Elpi Accumulate File "derive/derive.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, derive.main I O.
  main [str I] :- !, derive.main I I.
  main _ :- usage.

  usage :- coq.error ""Usage: derive <inductive type name> [<output module name>]"".
".
Elpi Typecheck.