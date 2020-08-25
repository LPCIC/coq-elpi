(* Unary parametricity translation.

   license: GNU Lesser General Public License Version 2.1 or later
   ------------------------------------------------------------------------- *)

From elpi Require Export elpi.

Definition contractible T := { x : T & forall y, @eq T x y }.

Register contractible as elpi.derive.contractible.

Definition contracts T P (x : T) w u := (@existT (P x) (fun u : P x => forall v : P x,@eq (P x) u v) w u).

Register contracts as elpi.derive.contracts.

Definition full T P := forall x : T, P x.

Register full as elpi.derive.full.

Definition trivial T P := forall x : T, contractible (P x).

Register trivial as elpi.derive.trivial.

Definition trivial_full T P (e : trivial T P) (x : T) : P x := projT1 (e x).

Register trivial_full as elpi.derive.trivial_full.

Definition trivial_uniq T P (e : trivial T P) (x : T) (p : P x) :
  trivial_full T P e x = p := projT2 (e x) p.

Register trivial_uniq as elpi.derive.trivial_uniq.

(* To be removed. Like the param1-db below, but readable from Coq *)
Class reali_db {X XR : Type} (x : X) (xR : XR) := store_reali {}.
Class reali {X : Type} {XR : X -> Type} (x : X) (xR : XR x) := Reali {}.

Register store_reali as param1.store_reali.

(* Links a term (constant, inductive type, inductive constructor) with
   its parametricity translation *)
Elpi Db derive.param1.db lp:{{

:index(3)
pred reali i:term, o:term.

:name "reali:fail"
reali X _ :-
  M is "derive.param1: No unary parametricity translation for " ^
          {coq.term->string X},
  stop M.

type realiR term -> term -> prop.

:name "realiR:fail"
realiR T TR :-
  M is "derive.param1: No unary parametricity translation linking " ^
          {coq.term->string T} ^ " and " ^ {coq.term->string TR},
  stop M.
}}.

Elpi Command derive.param1.
Elpi Accumulate File "coq-lib-extra.elpi".
Elpi Accumulate File "elpi/param1.elpi".
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I GR, derive.param1.main GR O _.
  main [str I] :- !, coq.locate I GR, derive.param1.main GR "is_" _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.param1 <object name> [<output prefix>]".
}}. 
Elpi Typecheck.


