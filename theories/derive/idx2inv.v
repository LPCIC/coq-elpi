(* Generates lemmas linking an inductive and its iverted form.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Import elpi derive.invert.

Elpi Db derive.idx2inv.db "
  type idx2inv-db term -> term -> term -> term -> prop.
".

Elpi Command derive.idx2inv.
Elpi Accumulate Db derive.invert.db.
Elpi Accumulate Db derive.idx2inv.db.
Elpi Accumulate File "derive/idx2inv.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, coq.locate I T, derive.idx2inv.main T O _.
  main [str I] :- !, coq.locate I T, derive.idx2inv.main T ""_to_"" _.
  main _ :- usage.

  usage :- coq.error ""Usage: derive.idx2inv <inductive type name> [<separator>]"".
".
Elpi Typecheck.
