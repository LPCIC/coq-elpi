(* Unary parametricity translation

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Import elpi.

(* To be removed. Like the param1-db below, but readable from Coq *)
Class reali_db {X XR : Type} (x : X) (xR : XR) := store_reali {}.
Class reali {X : Type} {XR : X -> Type} (x : X) (xR : XR x) := Reali {}.

(* Links a term (constant, inductive type, inductive constructor) with
   its parametricity translation *)
Elpi Db derive.param1.db " type param1-db term -> term -> prop. ".

Elpi Command derive.param1.
Elpi Accumulate File "coq-lib-extra.elpi".
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate File "derive/param1.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, coq.locate I T, derive.param1.main T O _.
  main [str I] :- !, coq.locate I T, derive.param1.main T ""R"" _.
  main _ :- usage.

  usage :- coq.error ""Usage: derive.param1 <object name> [<output suffix>]"".
". 
Elpi Typecheck.

Definition Arrow A B := A -> B.
Elpi derive.param1 Arrow Pred.

Elpi Db derive.param1.db "
  param1-db (prod _ S _\ T) (app [ArrR, S, SR, T, TR]) :-
    param1-db {{Arrow}} ArrR,
    param1-db S SR,
    param1-db T TR.
".

Definition UnitPred T (x : T) := True.
