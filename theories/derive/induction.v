(* Generates the induction principle.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Export elpi derive.param1 derive.param1P.

Definition UnitPred T (x : T) := True.
Definition UnitProof T x : UnitPred T x := I.

Elpi Db derive.induction.db " type induction-db term -> term -> prop. ".

Elpi Command derive.induction.
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1P.db.
Elpi Accumulate Db derive.induction.db.
Elpi Accumulate File "derive/induction.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, coq.locate I T, derive.induction.main T O _.
  main [str I] :- !,
    coq.locate I T, term->gr T GR, Name is {coq.gr->id GR} ^ ""_induction"",
    derive.induction.main T Name _.
  main _ :- usage.

  usage :-
    coq.error ""Usage: derive.induction <inductive type name> [<output name>]"".
".  
Elpi Typecheck.

