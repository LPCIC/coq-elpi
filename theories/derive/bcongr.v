(* Generates congruence lemmas using reflect

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From Coq Require Export Bool.
From elpi Require Export elpi derive.projK.

Elpi Db derive.bcongr.db "

type bcongr-db term -> term -> prop.

:name ""bcongr-db:fail""
bcongr-db T _ :-
  coq.say ""derive.bcongr: can't find the boolean congruence for constructor""
          {coq.term->string T},
  stop.

".

Elpi Command derive.bcongr.
Elpi Accumulate Db derive.bcongr.db.
Elpi Accumulate Db derive.projK.db.
Elpi Accumulate File "ltac/injection.elpi".
Elpi Accumulate File "derive/bcongr.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, coq.locate I T, derive.bcongr.main T O _.
  main [str I] :- !,
    coq.locate I T,
    coq.gr->id {term->gr T} Tname,
    Name is Tname ^ ""_bcongr_"",
    derive.bcongr.main T Name _.
  main _ :- usage.

  usage :- coq.error ""Usage: derive.bcongr <inductive type name> [<output name suffix>]"".
".
Elpi Typecheck. 
