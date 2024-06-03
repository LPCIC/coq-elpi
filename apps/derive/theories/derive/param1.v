(* Unary parametricity translation.

   license: GNU Lesser General Public License Version 2.1 or later
   ------------------------------------------------------------------------- *)
From elpi.apps.derive.elpi Extra Dependency "paramX_lib.elpi" as paramX.
From elpi.apps.derive.elpi Extra Dependency "param1.elpi" as param1.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

From elpi Require Import elpi.
From elpi.apps Require Import derive.

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

From Coq Require Import PrimInt63 PrimFloat.

Inductive is_uint63 : PrimInt63.int -> Type := uint63 (i : PrimInt63.int) : is_uint63 i.
Register is_uint63 as elpi.derive.is_uint63.

Inductive is_float64 : PrimFloat.float -> Type := float64 (f : PrimFloat.float ) : is_float64 f.
Register is_float64 as elpi.derive.is_float64.

(* Links a term (constant, inductive type, inductive constructor) with
   its parametricity translation *)
Elpi Db derive.param1.db lp:{{

pred reali-done i:gref.

:index(3)
pred reali i:term, o:term.

reali {{ lib:num.int63.type }} {{ lib:elpi.derive.is_uint63 }} :- !.
reali {{ lib:num.float.type }} {{ lib:elpi.derive.is_float64 }} :- !.

:name "reali:fail"
reali X _ :-
  M is "derive.param1: No unary parametricity translation for " ^
          {coq.term->string X},
  stop M.

type realiR term -> term -> prop.

realiR {{ lib:num.int63.type }} {{ lib:elpi.derive.is_uint63 }} :- !.
realiR {{ lib:num.float.type }} {{ lib:elpi.derive.is_float64 }} :- !.

:name "realiR:fail"
realiR T TR :-
  M is "derive.param1: No unary parametricity translation linking " ^
          {coq.term->string T} ^ " and " ^ {coq.term->string TR},
  stop M.
}}.

(* standalone *)
Elpi Command derive.param1.
Elpi Accumulate File derive_hook.
Elpi Accumulate File paramX.
Elpi Accumulate File param1.
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I GR, derive.param1.main GR "" _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.param1 <object name>".
}}. 
Elpi Typecheck.

Module Export exports.
Elpi derive.param1 eq.
End exports.
Register is_eq as elpi.derive.is_eq.


(* hook into derive *)
Elpi Accumulate derive File paramX.
Elpi Accumulate derive File param1.
Elpi Accumulate derive Db derive.param1.db.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "param1" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{
  
pred derive.on_param1 i:inductive, i:(inductive -> string -> list prop -> prop), i:string, o:list prop.
derive.on_param1 T F N C :- reali (global (indt T)) (global (indt P)), !, F P N C.

derivation T N ff (derive "param1" (derive.param1.main T N ) (reali-done T)).

}}.
