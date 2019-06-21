(* Generates inversion lemmas by encoding indexes with equations and non
   uniform parameters.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Export elpi.

Elpi Db derive.invert.db lp:{{ type invert-db term -> term -> prop. }}.

Elpi Command derive.invert.
Elpi Accumulate Db derive.invert.db.
Elpi Accumulate File "derive/invert.elpi".
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I GR, derive.invert.main (global GR) O _.
  main [str I] :- !, coq.locate I GR, derive.invert.main (global GR) "_inv" _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.invert <inductive type name> [<output name>]".
}}.
Elpi Typecheck.
