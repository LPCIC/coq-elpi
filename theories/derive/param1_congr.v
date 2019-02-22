(* Given an inductive type I and its unary parametricity translation IR it
   generates a proof IP that "forall i : I, IR i".

   It is used for the derivation of induction principles.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Export elpi derive.param1.

Elpi Db derive.param1.congr.db "
  type param1-congr-db term -> term -> prop. 
".

Elpi Command derive.param1.congr.
Elpi Accumulate File "coq-lib-extra.elpi".
Elpi Accumulate Db derive.param1.congr.db.
Elpi Accumulate File "derive/param1_congr.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, coq.locate I T, derive.param1.congr.main T O _.
  main [str I] :- !, coq.locate I T, derive.param1.congr.main T ""congr_"" _.
  main _ :- usage.

  usage :-
    coq.error ""Usage: derive.param1.congr <inductive type name> [<output prefix>]"".
".
Elpi Typecheck.
