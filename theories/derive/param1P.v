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

param1P-db (lam `f` (prod `_` S _\ T) f\
            prod `x` S x\ prod `px` (RS x) _) 
           (lam `f` (prod `_` S _\ T) f\
             lam `x` S x\
              lam `px` (RS x) _\ P f x) :-
           pi f x\
             reali T R,
             param1P-db R PT,
             mk-app PT [{mk-app f [x]}] (P f x).

".

Elpi Command derive.param1P.
Elpi Accumulate File "coq-lib-extra.elpi".
Elpi Accumulate File "derive/param1.elpi".
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1P.db.
Elpi Accumulate File "derive/param1P.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, coq.locate I T, derive.param1P.main T O _.
  main [str I] :- !,
    coq.locate I T,
    coq.gr->id {term->gr T} Tname,
    Name is Tname ^ ""_"",
    derive.param1P.main T {rex_replace ""^is_"" """" Name} _.
  main _ :- usage.

  usage :-
    coq.error ""Usage: derive.param1P <inductive type name> [<output suffix>]"".
". 
Elpi Typecheck.
