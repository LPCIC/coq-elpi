(* Generates congruence lemmas using reflect

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From Coq Require Export Bool.
From elpi Require Export elpi derive.projK.

Elpi Db derive.bcongr.db "

type bcongr-db @constructor -> term -> prop.

:name ""bcongr-db:fail""
bcongr-db K _ :-
  coq.say ""derive.bcongr: can't find the boolean congruence for constructor"" K,
  stop.

".

Elpi Command derive.bcongr.
Elpi Accumulate Db derive.bcongr.db.
Elpi Accumulate Db derive.projK.db.
Elpi Accumulate File "ltac/injection.elpi".
Elpi Accumulate File "derive/bcongr.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, coq.locate I GR, derive.bcongr.main (global GR) O _.
  main [str I] :- !,
    coq.locate I GR,
    coq.gr->id GR Tname,
    Name is Tname ^ ""_bcongr_"",
    derive.bcongr.main (global GR) Name _.
  main _ :- usage.

  usage :- coq.error ""Usage: derive.bcongr <inductive type name> [<output name suffix>]"".
".
Elpi Typecheck. 
