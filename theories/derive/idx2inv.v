(* Generates lemmas linking an inductive with indexes and its structural
   copy without indexes but equations instead.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Export elpi derive.invert.

Elpi Db derive.idx2inv.db lp:{{
  type idx2inv-db @inductive -> @inductive -> @constant -> @constant -> prop.
}}.

Elpi Command derive.idx2inv.
Elpi Accumulate Db derive.invert.db.
Elpi Accumulate Db derive.idx2inv.db.
Elpi Accumulate File "derive/idx2inv.elpi".
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I (indt GR), derive.idx2inv.main GR O _.
  main [str I] :- !, coq.locate I (indt GR), derive.idx2inv.main GR "_to_" _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.idx2inv <inductive type name> [<separator>]".
}}.
Elpi Typecheck.
