(* Generates comparison tests.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From Coq Require Import Bool.
From elpi Require Import elpi.

Elpi Db derive.eq.db "type eq-db term -> term -> term -> prop.".

Elpi Command derive.eq.
Elpi Accumulate Db derive.eq.db.
Elpi Accumulate File "derive/eq.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, coq.locate I T, derive.eq.main T O _.
  main [str I] :- !, 
    coq.locate I T, term->gr T GR, coq.gr->id GR Id, O is Id ^ ""_eq"",
    derive.eq.main T O _.
  main _ :- usage.

  usage :- coq.error ""Usage: derive.eq <inductive type name> [<output name>]"".
".
Elpi Typecheck.

