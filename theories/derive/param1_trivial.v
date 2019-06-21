(* Given an inductive type I and its unary parametricity translation is_ it
   generates a proof of forall i : I, { p : is_I i & forall q, p = q }.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Export elpi derive.param1 derive.param1_congr derive.param1_inhab. 

Elpi Db derive.param1.trivial.db lp:{{
type param1-trivial-db term -> term -> prop. 
param1-trivial-db (lam `f` (prod `_` S _\ T) f\
            prod `x` S x\ prod `px` (RS x) _) 
           (lam `f` (prod `_` S _\ T) f\
             lam `x` S x\
              lam `px` (RS x) _\ P f x) :-
           pi f x\
             reali T R,
             param1-trivial-db R PT,
             mk-app PT [{mk-app f [x]}] (P f x).

param1-trivial-db (app [Hd|Args]) (app[P|PArgs]) :-
  param1-trivial-db Hd P,
  param1-trivial-db-args Args PArgs.
  
type param1-trivial-db-args list term -> list term -> prop. 
param1-trivial-db-args [] [].
param1-trivial-db-args [T,P|Args] [T,P,Q|PArgs] :- param1-trivial-db P Q, param1-trivial-db-args Args PArgs.

}}.

Elpi Command derive.param1.trivial.
Elpi Accumulate File "coq-lib-extra.elpi".
Elpi Accumulate File "derive/param1.elpi".
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1.inhab.db.
Elpi Accumulate Db derive.param1.congr.db.
Elpi Accumulate Db derive.param1.trivial.db.
Elpi Accumulate File "derive/param1_trivial.elpi".
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I GR, derive.param1.trivial.main (global GR) O _.
  main [str I] :- !, coq.locate I GR, derive.param1.trivial.main (global GR) "_trivial" _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.param1.trivial <inductive type name> [<output suffix>]".
}}.
Elpi Typecheck.
