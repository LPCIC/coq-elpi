(* Given an inductive type I and its unary parametricity translation is_ it
   generates a proof of forall i : I, { p : is_I i & forall q, p = q }.

   license: GNU Lesser General Public License Version 2.1 or later
   ------------------------------------------------------------------------- *)

From elpi Require Export elpi.
From elpi.apps Require Export derive.param1 derive.param1_congr derive.param1_inhab.

Definition is_uint63_trivial : trivial Int63.int is_uint63 :=
  fun x => contracts _ is_uint63 x (is_uint63_witness x)
    (fun y => match y with uint63 i => eq_refl end).
Register is_uint63_trivial as elpi.derive.is_uint63_trivial.

Definition is_float64_trivial : trivial PrimFloat.float is_float64 :=
  fun x => contracts _ is_float64 x (is_float64_witness x)
    (fun y => match y with float64 i => eq_refl end).
Register is_float64_trivial as elpi.derive.is_float64_trivial.

Elpi Db derive.param1.trivial.db lp:{{
type param1-trivial-db term -> term -> prop.

param1-trivial-db {{ lib:elpi.derive.is_uint63 }} {{ lib:elpi.derive.is_uint63_trivial }}.
param1-trivial-db {{ lib:elpi.derive.is_float64 }} {{ lib:elpi.derive.is_float64_trivial }}.

param1-trivial-db (fun `f` (prod `_` S _\ T) f\
            prod `x` S x\ prod `px` (RS x) _)
           (fun `f` (prod `_` S _\ T) f\
             fun `x` S x\
              fun `px` (RS x) _\ P f x) :-
           pi f x\
             reali T R,
             param1-trivial-db R PT,
             coq.mk-app PT [{coq.mk-app f [x]}] (P f x).

param1-trivial-db (app [Hd|Args]) (app[P|PArgs]) :-
  param1-trivial-db Hd P,
  param1-trivial-db-args Args PArgs.

type param1-trivial-db-args list term -> list term -> prop.
param1-trivial-db-args [] [].
param1-trivial-db-args [T,P|Args] [T,P,Q|PArgs] :- param1-trivial-db P Q, param1-trivial-db-args Args PArgs.

}}.

Elpi Command derive.param1.trivial.
Elpi Accumulate File "paramX-lib.elpi".
Elpi Accumulate File "elpi/param1.elpi".
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1.inhab.db.
Elpi Accumulate Db derive.param1.congr.db.
Elpi Accumulate Db derive.param1.trivial.db.
Elpi Accumulate File "elpi/param1_trivial.elpi".
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I (indt GR), derive.param1.trivial.main GR O _.
  main [str I] :- !, coq.locate I (indt GR), derive.param1.trivial.main GR "_trivial" _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.param1.trivial <inductive type name> [<output suffix>]".
}}.
Elpi Typecheck.
