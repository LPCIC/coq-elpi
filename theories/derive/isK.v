From elpi Require Import elpi.

(** derive.isK generates a function per constructor that returns
    true iff it is applied to such constructor *)

Elpi Db derive.isK.db " type isK-db @gref -> term -> prop. ".

Elpi Command derive.isK.
Elpi Accumulate Db derive.isK.db.
Elpi Accumulate File "derive/isK.elpi".
Elpi Accumulate "
  main [str I,str O] :- !, derive.isK.main I O _.
  main [str I] :- !, derive.isK.main I ""is"" _.
  main _ :- usage.

  usage :- coq.error ""Usage: derive.isK <inductive type name> [<output prefix>]"".
".
Elpi Typecheck.
