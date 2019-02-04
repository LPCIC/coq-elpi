(* Generates inversion lemmas by encoding indexes with equations and non
   uniform parameters.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Export elpi.

Elpi Db derive.invert.db "type invert-db term -> term -> prop.".

Elpi Command derive.invert.
Elpi Accumulate Db derive.invert.db.
Elpi Accumulate File "derive/invert.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, coq.locate I T, derive.invert.main T O _.
  main [str I] :- !, coq.locate I T, derive.invert.main T ""_inv"" _.
  main _ :- usage.

  usage :- coq.error ""Usage: derive.invert <inductive type name> [<output name>]"".
".
Elpi Typecheck.
