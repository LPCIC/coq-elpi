(* Generates the induction principle.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Export elpi derive.param1 derive.param1_inhab derive.param1_trivial derive.eqK derive.eqcorrect.

Elpi Command derive.eqOK.

Elpi Accumulate File "coq-lib-extra.elpi".
Elpi Accumulate File "derive/param1.elpi".
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1.inhab.db.
Elpi Accumulate Db derive.param1.trivial.db.
Elpi Accumulate Db derive.eqcorrect.db.

Elpi Accumulate File "derive/eqOK.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, coq.locate I T, derive.eqOK.main T O _.
  main [str I] :- !,
    coq.locate I T, term->gr T GR, Name is {coq.gr->id GR} ^ ""_eq_OK"",
    derive.eqOK.main T Name _.
  main _ :- usage.

  usage :-
    coq.error ""Usage: derive.eqOK <inductive name> [<output name>]"".
".  
Elpi Typecheck.

