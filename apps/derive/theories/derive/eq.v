(* Generates equality tests.

   license: GNU Lesser General Public License Version 2.1 or later
   ------------------------------------------------------------------------- *)

From Coq Require Export Bool.
From elpi Require Export elpi.

Register Coq.Numbers.Cyclic.Int63.Int63.eqb as elpi.derive.eq_unit63.
Register Coq.Floats.PrimFloat.eqb as elpi.derive.eq_float64.

Elpi Db derive.eq.db lp:{{

type eq-db term -> term -> term -> prop.
eq-db {{ lib:elpi.uint63 }} {{ lib:elpi.uint63 }} {{ lib:elpi.derive.eq_unit63 }} :- !.
eq-db {{ lib:elpi.float64 }} {{ lib:elpi.float64 }} {{ lib:elpi.derive.eq_float64 }} :- !.

:name "eq-db:fail"
eq-db A B F :-
  ((whd1 A A1, B1 = B); (whd1 B B1, A1 = A)), !,
  eq-db A1 B1 F.

eq-db A B _ :-
  M is "derive.eq: can't find the comparison function for terms of type " ^
          {coq.term->string A} ^ " and " ^ {coq.term->string B} ^ " respectively",
  stop M.
}}.

Elpi Command derive.eq.
Elpi Accumulate Db derive.eq.db.
Elpi Accumulate File "elpi/eq.elpi".
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I (indt GR), derive.eq.main GR O _.
  main [str I] :- !, 
    coq.locate I (indt GR), coq.gref->id (indt GR) Id, O is Id ^ "_eq",
    derive.eq.main GR O _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.eq <inductive type name> [<output name>]".
}}.
Elpi Typecheck.

