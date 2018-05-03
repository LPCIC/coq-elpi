(* Generates the induction principle.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Import elpi derive.param1 derive.param1P derive.induction.

Elpi Command derive.unitsimplifier.
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1P.db.
Elpi Accumulate File "derive/unitsimplifier.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, derive.unitsimplifier.main I O _.
  main [str I] :- !,
    coq.locate I T, term->gr T GR, Name is {coq.gr->id GR} ^ ""_simple"",
    derive.unitsimplifier.main I Name _.
  main _ :- usage.

  usage :-
    coq.error ""Usage: derive.unitsimplifier <term name> [<output name>]"".
".  
Elpi Typecheck.

