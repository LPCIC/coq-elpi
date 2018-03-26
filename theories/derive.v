From elpi Require Export derive.eq derive.isK derive.map derive.projK.

Elpi Command derive.
Elpi Accumulate Db derive.eq.db.
Elpi Accumulate Db derive.isK.db.
Elpi Accumulate Db derive.map.db.
Elpi Accumulate Db derive.projK.db.
Elpi Accumulate File "derive/derive.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, derive.main I O.
  main [str I] :- !, derive.main I I.
  main _ :- usage.

  usage :- coq.error ""Usage: derive <inductive type name> [<output module name>]"".
".
Elpi Typecheck.
