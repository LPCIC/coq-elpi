(* Draft: trivil eq_axiom (needed for indexes)

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From mathcomp Require Import all_ssreflect.
From elpi Require Import elpi.

Definition transp {T} (Ctx : T -> Type) {t1 t2} (e : t2 = t1) : Ctx t1 -> Ctx t2.
Proof. by case: _/e. Defined.

Axiom dep_fun_ext : forall T (P : T -> Type) (f g: forall t:T, P t), (forall x, f x = g x) -> f = g.

Lemma reflect_irrelevance (T : eqType) (x y : T) b (p1 p2 : reflect (x = y) b) : p1 = p2.
Proof.
case: p2 p1 => {b} [e| ne] r.
  refine  (match r as r in reflect _ t
           return forall p : t = true, r = 
               transp (reflect (x = y)) p (ReflectT (x = y) e) with 
           | ReflectT e' => _
           | ReflectF ne' => _
           end (erefl true)) => // p {r}.
  rewrite (eq_irrelevance p (erefl true)) {p}.
  congr (ReflectT (x = y)).
  by apply: eq_irrelevance.
refine  (match r as r in reflect _ t
           return forall p : t = false, r = 
               transp (reflect (x = y)) p (ReflectF (x = y) ne) with 
           | ReflectT e' => _
           | ReflectF ne' => _
           end (erefl false)) => // p {r}.
rewrite (eq_irrelevance p (erefl false)) {p}.
congr (ReflectF (x = y)).
apply: dep_fun_ext.
by case/ne.
Qed.

Lemma eq_axiom_trivial (a : eqType) fa :
  full a (eq_axiom a fa) -> trivial a (eq_axiom a fa).
Proof.
rewrite /eq_axiom /full.
move=> p1 x; exists (p1 x) => p2.
apply: dep_fun_ext => w.
apply: reflect_irrelevance.
Qed.

