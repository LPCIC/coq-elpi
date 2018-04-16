(* For each constructor K the function isK returns true iff it is applied
   to K. These helpers are use to implement "discriminate".

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Import elpi.

(* Links the @gref of the constructor K to the isK constant *)
Elpi Db derive.isK.db " type isK-db @gref -> term -> prop. ".

Elpi Command derive.isK.
Elpi Accumulate Db derive.isK.db.
Elpi Accumulate File "derive/isK.elpi".
Elpi Accumulate "
  main [str I,str O] :- !, derive.isK.main I O _.
  main [str I] :- !, derive.isK.main I ""is"" _.
  main _ :- usage.

  usage :-
    coq.error ""Usage: derive.isK <inductive type name> [<output prefix>]"".
".
Elpi Typecheck.
