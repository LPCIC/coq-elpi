(* For each constructor K the function isK returns true iff it is applied
   to K. These helpers are use to implement "discriminate".

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Export elpi.

(* Links the @gref of the constructor K to the isK constant *)
Elpi Db derive.isK.db lp:{{ type isK-db @constructor -> term -> prop. }}.

Elpi Command derive.isK.
Elpi Accumulate Db derive.isK.db.
Elpi Accumulate File "derive/isK.elpi".
Elpi Accumulate lp:{{
  main [str I,str O] :- !, coq.locate I GR, derive.isK.main (global GR) O _.
  main [str I] :- !,
    coq.locate I GR,
    Prefix is {coq.gr->id GR} ^ "_is_",
    derive.isK.main (global GR) Prefix _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.isK <inductive type name> [<output prefix>]".
}}.
Elpi Typecheck.
