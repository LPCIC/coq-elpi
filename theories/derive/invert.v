(* Generates inversion lemmas by encoding indexes with equations and non
   uniform parameters.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Import elpi.

Elpi Db derive.invert.db "type invert-db term -> term -> prop.".

Elpi Command derive.invert.
Elpi Accumulate Db derive.invert.db.
Elpi Accumulate File "derive/invert.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, coq.locate I T, derive.invert.main T O _.
  main [str I] :- !, 
    coq.locate I T, term->gr T GR, coq.gr->id GR Id, O is Id ^ ""_inv"",
    derive.invert.main T O _.
  main _ :- usage.

  usage :- coq.error ""Usage: derive.invert <inductive type name> [<output name>]"".
".
Elpi Typecheck.
Check negb.
Inductive test : bool -> Type :=
  K1 : test true
| K2 : forall x, test (negb x) -> test (negb (negb x)).


Elpi derive.invert test. 