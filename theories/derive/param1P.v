(* Given an inductive type I and its unary parametricity translation IR it
   generates a proof IP that "forall i : I, IR i".

   It is used for the derivation of induction principles.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Import elpi derive.param1.


Definition UnitProof T x : UnitPred T x := I.

Elpi Db derive.param1P.db " type param1P-db term -> term -> prop. 

param1P-db {{ @elpi.derive.param1.UnitPred lp:S }}
           {{ @elpi.derive.param1P.UnitProof lp:S }}.

param1P-db {{ @elpi.derive.param1.ArrowPred lp:S lp:RS lp:T lp:RT }}
           (lam `f` (prod `_` S _\ T) f\
             lam `s` S s\
              lam `_` (RSs s) _\ P f s) :-
           pi f s\
             mk-app RS [s] (RSs s),
             param1P-db RT PT,
             mk-app PT [{mk-app f [s]}] (P f s).

".

Elpi Command derive.param1P.
Elpi Accumulate Db derive.param1P.db.
Elpi Accumulate File "derive/param1P.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, coq.locate I T, derive.param1P.main T O _.
  main [str I] :- !, coq.locate I T, derive.param1P.main T ""P"" _.
  main _ :- usage.

  usage :-
    coq.error ""Usage: derive.param1P <inductive type name> [<output suffix>]"".
". 
Elpi Typecheck.

