(* Given an inductive type I and its unary parametricity translation is_ it
   generates a proof of 
     forall i : I, is_U i
   and then a proof of
     forall i : I, { p : is_I i & forall q, p = q }.

   license: GNU Lesser General Public License Version 2.1 or later
   ------------------------------------------------------------------------- *)
From elpi.apps.derive.elpi Extra Dependency "paramX_lib.elpi" as paramX.
From elpi.apps.derive.elpi Extra Dependency "param1.elpi" as param1.
From elpi.apps.derive.elpi Extra Dependency "param1_inhab.elpi" as param1_inhab.
From elpi.apps.derive.elpi Extra Dependency "param1_trivial.elpi" as param1_trivial.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

From elpi Require Import elpi.
From elpi.apps Require Import derive.param1 derive.param1_congr.

  Elpi Db derive.param1.trivial.db lp:{{

  func param1-trivial-done inductive ->.
  type param1-trivial-db term -> term -> prop.
  type param1-trivial-db-args list term -> list term -> prop.

  func param1-inhab-done inductive ->.
  type param1-inhab-db term -> term -> prop.
  type param1-inhab-db-args list term -> list term -> prop.

}}.
#[superglobal] Elpi Accumulate derive.param1.trivial.db Db Header derive.param1.db.
#[superglobal] Elpi Accumulate derive.param1.trivial.db lp:{{

  :name "param1:inhab:start"
  param1-inhab-db (fun `f` (prod `_` S _\ T) f\
              prod `x` S x\ prod `px` (RS x) _)
            (fun `f` (prod `_` S _\ T) f\
              fun `x` S x\
                fun `px` (RS x) _\ P f x) :-
            pi f x\
              reali T R,
              param1-inhab-db R PT,
              coq.mk-app PT [{coq.mk-app f [x]}] (P f x).

  param1-inhab-db (app [Hd|Args]) (app[P|PArgs]) :-
    param1-inhab-db Hd P, !,
    param1-inhab-db-args Args PArgs.
  
  param1-inhab-db-args [] [].
  param1-inhab-db-args [T,P|Args] R :-
    std.assert-ok! (coq.typecheck T Ty) "param1-inhab-db: cannot work illtyped term",
    if (coq.sort? Ty)
       (param1-inhab-db P Q, R = [T,P,Q|PArgs], param1-inhab-db-args Args PArgs)
       (R = [T,P|PArgs], param1-inhab-db-args Args PArgs).
   
  :name "param1:trivial:start"
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
    param1-trivial-db Hd P, !,
    param1-trivial-db-args Args PArgs.

  param1-trivial-db-args [] [].
  param1-trivial-db-args [T,P|Args] R :-
    std.assert-ok! (coq.typecheck T Ty) "param1-trivial-db: cannot work on illtyped term",
    if (coq.sort? Ty)
      (param1-trivial-db P Q, R = [T,P,Q|PArgs], param1-trivial-db-args Args PArgs)
      (R = [T,P|PArgs], param1-trivial-db-args Args PArgs).

}}.
  

(* standalone *)
Elpi Command derive.param1.trivial.
Elpi Accumulate File derive_hook.
Elpi Accumulate File paramX.
Elpi Accumulate File param1.
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1.congr.db.
Elpi Accumulate Db derive.param1.trivial.db.
Elpi Accumulate File param1_inhab.
Elpi Accumulate File param1_trivial.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I (indt GR),
    derive.param1.inhab.main GR "_inhab" CL,
    CL => derive.param1.trivial.main GR "_trivial" _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.param1.trivial <inductive type name>".
}}.

 
Elpi Command derive.param1.inhab.
Elpi Accumulate File derive_hook.
Elpi Accumulate File paramX.
Elpi Accumulate File param1.
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1.congr.db.
Elpi Accumulate Db derive.param1.trivial.db.
Elpi Accumulate File param1_inhab.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I (indt GR),
    derive.param1.inhab.main GR "_inhab" _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.param1.inhab <inductive type name>".
}}.

(* ad-hoc rules for primitive data, eq and is_true *)

Module Export exports.
Elpi derive.param1.trivial is_bool.
End exports.

Definition is_uint63_inhab x : is_uint63 x. Proof. constructor. Defined.
Register is_uint63_inhab as elpi.derive.is_uint63_inhab.

Definition is_float64_inhab x : is_float64 x. Proof. constructor. Defined.
Register is_float64_inhab as elpi.derive.is_float64_inhab.

Definition is_pstring_inhab s : is_pstring s. Proof. constructor. Defined.
Register is_pstring_inhab as elpi.derive.is_pstring_inhab.

Definition is_eq_inhab
  A (PA : A -> Type) (HA : trivial A PA) (x : A) (px: PA x) y (py : PA y) (eq_xy : x = y) :
    is_eq A PA x px y py eq_xy.
Proof.
  revert py.
  case eq_xy; clear eq_xy y.
  intro py.
  rewrite <- (trivial_uniq A PA HA x px); clear px.
  rewrite <- (trivial_uniq A PA HA x py); clear py.
  apply (is_eq_refl A PA x (trivial_full A PA HA x)).
Defined.
Register is_eq_inhab as elpi.derive.is_eq_inhab.

Definition is_true_inhab b (H : is_bool b) p : is_is_true b H p :=
  is_eq_inhab bool is_bool is_bool_trivial b H true is_true p.
Register is_true_inhab as elpi.derive.is_true_inhab.


Elpi Accumulate derive.param1.trivial.db lp:{{

  :before "param1:inhab:start"
  param1-inhab-db {{ lib:elpi.derive.is_uint63 }} {{ lib:elpi.derive.is_uint63_inhab }}.
  :before "param1:inhab:start"
  param1-inhab-db {{ lib:elpi.derive.is_float64 }} {{ lib:elpi.derive.is_float64_inhab }}.
  :before "param1:inhab:start"
  param1-inhab-db {{ lib:elpi.derive.is_pstring }} {{ lib:elpi.derive.is_pstring_inhab }}.
  :before "param1:inhab:start"
  param1-inhab-db {{ lib:elpi.derive.is_eq }} {{ lib:elpi.derive.is_eq_inhab }}.
  :before "param1:inhab:start"
  param1-inhab-db {{ lib:elpi.derive.is_true }} {{ lib:elpi.derive.is_true_inhab }}.


  :before "param1:inhab:start"
  param1-inhab-db
    {{ lib:elpi.derive.is_eq lp:A lp:PA lp:X lp:PX lp:Y lp:PY }}
    {{ lib:elpi.derive.is_eq_inhab lp:A lp:PA lp:QA lp:X lp:PX lp:Y lp:PY }} :- !,
    param1-trivial-db PA QA.

  :before "param1:inhab:start"
  param1-inhab-db {{ lib:elpi.derive.is_is_true lp:B lp:PB }} R :- !,
    param1-inhab-db {{ lib:elpi.derive.is_eq lib:elpi.bool lib:elpi.derive.is_bool lp:B lp:PB lib:elpi.true lib:elpi.derive.is_true }} R.

}}.


Definition is_uint63_trivial : trivial PrimInt63.int is_uint63 :=
  fun x => contracts _ is_uint63 x (is_uint63_inhab x)
    (fun y => match y with uint63 i => eq_refl end).
Register is_uint63_trivial as elpi.derive.is_uint63_trivial.
  
Definition is_float64_trivial : trivial PrimFloat.float is_float64 :=
  fun x => contracts _ is_float64 x (is_float64_inhab x)
    (fun y => match y with float64 i => eq_refl end).
Register is_float64_trivial as elpi.derive.is_float64_trivial.

Definition is_pstring_trivial : trivial lib:elpi.pstring is_pstring :=
  fun x => contracts _ is_pstring x (is_pstring_inhab x)
    (fun y => match y with pstring i => eq_refl end).
Register is_pstring_trivial as elpi.derive.is_pstring_trivial.

Lemma is_eq_trivial A (PA : A -> Type) (HA : trivial A PA) (x : A) (px: PA x) 
   y (py : PA y)
  : trivial (x = y) (is_eq A PA x px y py).
Proof.
  intro p.
  apply (contracts (x = y) (is_eq A PA x px y py) p (is_eq_inhab A PA HA x px y py p)).
  revert py.
  case p; clear p y.
  rewrite <- (trivial_uniq _ _ HA x px). clear px.
  intros py.
  rewrite <- (trivial_uniq _ _ HA x py). clear py.
  intro v; case v; clear v.
  unfold is_eq_inhab.
  unfold trivial_full.
  unfold trivial_uniq.
  case (HA x); intros it def_it; compute.
  case (def_it it).
  reflexivity.
Defined.
Register is_eq_trivial as elpi.derive.is_eq_trivial.

Definition is_true_trivial b (H : is_bool b) : trivial (lib:elpi.is_true b) (is_is_true b H) :=
  is_eq_trivial bool is_bool is_bool_trivial b H true is_true.
Register is_true_trivial as elpi.derive.is_true_trivial.


Elpi Accumulate derive.param1.trivial.db lp:{{

  :before "param1:trivial:start"
  param1-trivial-db {{ lib:elpi.derive.is_uint63 }} {{ lib:elpi.derive.is_uint63_trivial }}.
  :before "param1:trivial:start"
  param1-trivial-db {{ lib:elpi.derive.is_float64 }} {{ lib:elpi.derive.is_float64_trivial }}.
  :before "param1:trivial:start"
  param1-trivial-db {{ lib:elpi.derive.is_pstring }} {{ lib:elpi.derive.is_pstring_trivial }}.
  :before "param1:trivial:start"
  param1-trivial-db {{ lib:elpi.derive.is_eq }} {{ lib:elpi.derive.is_eq_trivial }}.
  :before "param1:trivial:start"
  param1-trivial-db {{ lib:elpi.derive.is_true }} {{ lib:elpi.derive.is_true_trivial }}.


  :before "param1:trivial:start"
  param1-trivial-db
    {{ lib:elpi.derive.is_eq lp:A lp:PA lp:X lp:PX lp:Y lp:PY }}
    {{ lib:elpi.derive.is_eq_trivial lp:A lp:PA lp:QA lp:X lp:PX lp:Y lp:PY }} :-
    param1-trivial-db PA QA.

  :before "param1:trivial:start"
  param1-trivial-db {{ lib:elpi.derive.is_is_true lp:B lp:PB }} R :- !,
    param1-trivial-db {{ lib:elpi.derive.is_eq lib:elpi.bool lib:elpi.derive.is_bool lp:B lp:PB lib:elpi.true lib:elpi.derive.is_true }} R.

}}.

(* hook into derive *)
Elpi Accumulate derive Db derive.param1.trivial.db.
Elpi Accumulate derive File param1_inhab.
Elpi Accumulate derive File param1_trivial.

#[phases="both"] Elpi Accumulate derive lp:{{
dep1 "param1_trivial" "param1_inhab".
dep1 "param1_trivial" "param1_congr".
dep1 "param1_inhab" "param1".
}}.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "param1_inhab" (cl\ cl = []) true).
  derivation _ _ (derive "param1_trivial" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{

derivation (indt T) _ ff (derive "param1_inhab"   (derive.on_param1 T derive.param1.inhab.main   "_inhab") (derive.on_param1 T (T\_\_\param1-inhab-done T) _ _)).
derivation (indt T) _ ff (derive "param1_trivial" (derive.on_param1 T derive.param1.trivial.main "_trivial") (derive.on_param1 T (T\_\_\param1-trivial-done T) _ _)).

}}.
