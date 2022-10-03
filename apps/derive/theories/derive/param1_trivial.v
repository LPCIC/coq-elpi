(* Given an inductive type I and its unary parametricity translation is_ it
   generates a proof of 
     forall i : I, is_U i
   and then a proof of
     forall i : I, { p : is_I i & forall q, p = q }.

   license: GNU Lesser General Public License Version 2.1 or later
   ------------------------------------------------------------------------- *)
From elpi.apps.derive Extra Dependency "paramX_lib.elpi" as paramX.
From elpi.apps.derive Extra Dependency "param1.elpi" as param1.
From elpi.apps.derive Extra Dependency "param1_inhab.elpi" as param1_inhab.
From elpi.apps.derive Extra Dependency "param1_trivial.elpi" as param1_trivial.

From elpi Require Export elpi.
From elpi.apps Require Export derive.param1 derive.param1_congr.

  
Definition is_uint63_witness x : is_uint63 x. Proof. constructor. Defined.
Register is_uint63_witness as elpi.derive.is_uint63_witness.

Definition is_float64_witness x : is_float64 x. Proof. constructor. Defined.
Register is_float64_witness as elpi.derive.is_float64_witness.

Definition is_eq_witness
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
Register is_eq_witness as elpi.derive.is_eq_witness.

Definition is_uint63_trivial : trivial PrimInt63.int is_uint63 :=
  fun x => contracts _ is_uint63 x (is_uint63_witness x)
    (fun y => match y with uint63 i => eq_refl end).
Register is_uint63_trivial as elpi.derive.is_uint63_trivial.
  
Definition is_float64_trivial : trivial PrimFloat.float is_float64 :=
  fun x => contracts _ is_float64 x (is_float64_witness x)
    (fun y => match y with float64 i => eq_refl end).
Register is_float64_trivial as elpi.derive.is_float64_trivial.

Lemma is_eq_trivial A (PA : A -> Type) (HA : trivial A PA) (x : A) (px: PA x) 
   y (py : PA y)
  : trivial (x = y) (is_eq A PA x px y py).
Proof.
  intro p.
  apply (contracts (x = y) (is_eq A PA x px y py) p (is_eq_witness A PA HA x px y py p)).
  revert py.
  case p; clear p y.
  rewrite <- (trivial_uniq _ _ HA x px). clear px.
  intros py.
  rewrite <- (trivial_uniq _ _ HA x py). clear py.
  intro v; case v; clear v.
  unfold is_eq_witness.
  unfold trivial_full.
  unfold trivial_uniq.
  case (HA x); intros it def_it; compute.
  case (def_it it).
  reflexivity.
Defined.
Register is_eq_trivial as elpi.derive.is_eq_trivial.

Elpi Db derive.param1.trivial.db lp:{{
  type param1-inhab-db term -> term -> prop.
  
  param1-inhab-db {{ lib:elpi.derive.is_uint63 }} {{ lib:elpi.derive.is_uint63_witness }}.
  param1-inhab-db {{ lib:elpi.derive.is_float64 }} {{ lib:elpi.derive.is_float64_witness }}.
  param1-inhab-db {{ lib:elpi.derive.is_eq }} {{ lib:elpi.derive.is_eq_witness }}.

  param1-inhab-db (fun `f` (prod `_` S _\ T) f\
              prod `x` S x\ prod `px` (RS x) _)
            (fun `f` (prod `_` S _\ T) f\
              fun `x` S x\
                fun `px` (RS x) _\ P f x) :-
            pi f x\
              reali T R,
              param1-inhab-db R PT,
              coq.mk-app PT [{coq.mk-app f [x]}] (P f x).
              
  param1-inhab-db
    {{ lib:elpi.derive.is_eq lp:A lp:PA lp:X lp:PX lp:Y lp:PY }}
    {{ lib:elpi.derive.is_eq_witness lp:A lp:PA lp:QA lp:X lp:PX lp:Y lp:PY }} :- !,
    param1-trivial-db PA QA.

  param1-inhab-db (app [Hd|Args]) (app[P|PArgs]) :-
    param1-inhab-db Hd P, !,
    param1-inhab-db-args Args PArgs.
  
  type param1-inhab-db-args list term -> list term -> prop.
  param1-inhab-db-args [] [].
  param1-inhab-db-args [T,P|Args] R :-
    std.assert-ok! (coq.typecheck T Ty) "param1-inhab-db: cannot work illtyped term",
    if (coq.sort? Ty)
       (param1-inhab-db P Q, R = [T,P,Q|PArgs], param1-inhab-db-args Args PArgs)
       (R = [T,P|PArgs], param1-inhab-db-args Args PArgs).
   
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

param1-trivial-db
   {{ lib:elpi.derive.is_eq lp:A lp:PA lp:X lp:PX lp:Y lp:PY }}
   {{ lib:elpi.derive.is_eq_trivial lp:A lp:PA lp:QA lp:X lp:PX lp:Y lp:PY }} :-
   param1-trivial-db PA QA.

param1-trivial-db (app [Hd|Args]) (app[P|PArgs]) :-
  param1-trivial-db Hd P, !,
  param1-trivial-db-args Args PArgs.

type param1-trivial-db-args list term -> list term -> prop.
param1-trivial-db-args [] [].
param1-trivial-db-args [T,P|Args] R :-
  std.assert-ok! (coq.typecheck T Ty) "param1-trivial-db: cannot work on illtyped term",
  if (coq.sort? Ty)
     (param1-trivial-db P Q, R = [T,P,Q|PArgs], param1-trivial-db-args Args PArgs)
     (R = [T,P|PArgs], param1-trivial-db-args Args PArgs).

}}.
  
Elpi Command derive.param1.trivial.
Elpi Accumulate File paramX.
Elpi Accumulate File param1.
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1.congr.db.
Elpi Accumulate Db derive.param1.trivial.db.
Elpi Accumulate File param1_inhab.
Elpi Accumulate File param1_trivial.
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I (indt GR),
    derive.param1.inhab.main GR O CL,
    CL => derive.param1.trivial.main GR O _.
  main [str I] :- !, coq.locate I (indt GR),
    derive.param1.inhab.main GR "_witness" CL,
    CL => derive.param1.trivial.main GR "_trivial" _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.param1.trivial <inductive type name> [<output suffix>]".
}}.
Elpi Typecheck.
