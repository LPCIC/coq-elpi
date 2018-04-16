(* Generates a projection for each argument of each constructor.

   The projection is expected to be applied to an explicit construcor and all
   its arguments. It is used to implement "injection".

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Import elpi.

Elpi Db derive.projK.db " type projK-db @gref -> int -> term -> prop. ".

Elpi Command derive.projK.
Elpi Accumulate Db derive.projK.db.
Elpi Accumulate File "derive/projK.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, derive.projK.main I O _.
  main [str I] :- !, derive.projK.main I ""proj"" _.
  main _ :- usage.

  usage :-
    coq.error ""Usage: derive.projK <inductive type name> [<output prefix>]"".
".
Elpi Typecheck.
