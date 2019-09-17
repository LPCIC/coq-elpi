(* Generates equality tests.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From Coq Require Export Bool.
From elpi Require Export elpi.

Elpi Db derive.eq.db lp:{{

type eq-db term -> term -> term -> prop.


:name "eq-db:fail"
eq-db A B F :-
  ((whd1 A A1, B1 = B); (whd1 B B1, A1 = A)), !,
  eq-db A1 B1 F.

eq-db A B _ :-
  coq.say "derive.eq: can't find the comparison function for terms of type"
          {coq.term->string A} "and" {coq.term->string B} "respectively",
  stop.
}}.

Elpi Command derive.eq.
Elpi Accumulate Db derive.eq.db.
Elpi Accumulate File "derive/eq.elpi".
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I (indt GR), derive.eq.main GR O _.
  main [str I] :- !, 
    coq.locate I (indt GR), coq.gr->id (indt GR) Id, O is Id ^ "_eq",
    derive.eq.main GR O _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.eq <inductive type name> [<output name>]".
}}.
Elpi Typecheck.

