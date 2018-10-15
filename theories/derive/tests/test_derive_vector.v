From elpi Require Import derive.

From elpi Require Import test_derive_stdlib.

Elpi derive.projK Coverage.vect.

Check projVCons3 :
forall A n, A -> forall m,
  Coverage.vect A m ->
    Coverage.vect A n -> {i1 : Coverage.peano & Coverage.vect A i1}.

(*
Elpi derive.bcongr Coverage.vect (* FIXME partial *).
*)

From mathcomp Require Import all_ssreflect.



Elpi derive.eq Coverage.peano.
Axiom peano_eqP : forall a b : Coverage.peano, reflect (a = b) (peano_eq a b).

Print Equality.mixin_of.
Canonical peano_eqMixin := Equality.Mixin peano_eqP.
Canonical peano_eqType := Equality.Pack peano_eqMixin Coverage.peano.


Lemma bcongr_VNil A :
   reflect (existT _ _ (Coverage.VNil A) = existT _ _ (Coverage.VNil A)) true.
Proof. by constructor. Qed.

Lemma bcongr_VCons :
  forall A,
  forall (a1 a2 : A) b1, reflect (a1 = a2) b1 ->
  forall (n1 n2 : Coverage.peano) b2, reflect (n1 = n2) b2 ->
  forall (v1 : Coverage.vect A n1) (v2 : Coverage.vect A n2) b3,
    reflect (existT _ n1 v1 = existT _ n2 v2) b3 ->
  reflect (existT _ _ (Coverage.VCons A a1 n1 v1) = 
          existT _ _ (Coverage.VCons A a2 n2 v2)) [&& b1 , b2 & b3].
Proof.
move=> A a1 a2 b1 [->|abs1] n1 n2 b2 [E2|abs2]; try case: _ / E2 => v1 v2 b3 [E3|abs3]; constructor.
  by have /= <- := (projT2_eq E3); rewrite [projT1_eq _]eq_axiomK /=.
  by move=> abs; apply: abs3; have /=  := (projT2_eq abs); rewrite [projT1_eq _]eq_axiomK /= => [= -> ].
  by move=> abs; apply: abs2; have [= -> ] := (projT1_eq abs).
  by move=> abs; apply: abs1; have /= := (projT2_eq abs); rewrite [projT1_eq _]eq_axiomK /= => [= -> ].
  by move=> abs; apply: abs1; have /= := (projT2_eq abs); rewrite [projT1_eq _]eq_axiomK /= => [= -> ].
  by move=> abs; apply: abs2; have [= -> ] := (projT1_eq abs).
Qed.

Elpi derive.eq Coverage.vect.

Fixpoint vect_eq_sig A f (v1 v2 : {n & Coverage.vect A n}) : bool := 
  let: existT n1 v1 := v1 in
  let: existT n2 v2 := v2 in
  if (peano_eqP n1 n2) is ReflectT e then vect_eq A f n2 (match e with erefl => v1 end) v2
  else false.

Elpi derive.param1 Coverage.peano.
Elpi derive.param1 Coverage.vect.
Elpi derive.induction Coverage.peano.
Elpi derive.induction Coverage.vect.

Elpi derive.projK sigT.

Lemma bridge A f n v : axiom {n & Coverage.vect A n} (vect_eq_sig A f) (existT _ n v) -> 
    axiom (Coverage.vect A n) (vect_eq A f n) v.
Proof.
move=> E y; move: (E (existT _ n y)) => /= {E}.
  case: peano_eqP => // p.
  rewrite [p]eq_axiomK /=.
  case=> [H|abs]; constructor.
    by move: (projT2_eq H); rewrite [projT1_eq _]eq_axiomK /= => <-.
  by move=> E; apply: abs; rewrite E.
Qed.

Lemma bridge2 A f n v : 
    axiom (Coverage.vect A n) (vect_eq A f n) v ->
    axiom {n & Coverage.vect A n} (vect_eq_sig A f) (existT _ n v).
Proof.
move=> E [m w]; rewrite /vect_eq_sig /=.
case: peano_eqP => //= e.
  case: _ / e w => /= w. case: (E w) => [->|abs]; constructor => // H.
  by apply: abs; move: (projT2_eq H); rewrite [projT1_eq _]eq_axiomK /= => <-.
constructor=> abs; apply: e. apply: projT1_eq abs.
Qed.


Lemma axiom_VNil : forall (A : Type) (f : A -> A -> bool) x,
  axiom_at {n & Coverage.vect A n} (vect_eq_sig A f) (existT _ Coverage.Zero (Coverage.VNil A)) x.
Proof.
move=> A f [n1 [|*]]; rewrite /axiom_at /vect_eq_sig /=; case: peano_eqP => //= e.
  rewrite [e]eq_axiomK /=; constructor; exact: bcongr_VNil.
by constructor=> abs; move: (projT1_eq abs) => /=.
Qed.

Lemma axiom_VCons : forall A f a n xs, 
 axiom A f a
 ->
 axiom {n : Coverage.peano & Coverage.vect A n} 
       (vect_eq_sig A f) (existT [eta Coverage.vect A] n xs)
 ->
axiom {n0 : Coverage.peano & Coverage.vect A n0} (vect_eq_sig A f)
  (existT [eta Coverage.vect A] (Coverage.Succ n) (Coverage.VCons A a n xs)).
Proof.
move=> A f a n v Hf H [m [|b w]]; rewrite /vect_eq_sig; case: peano_eqP => //= e.
  by constructor=> abs; apply: e; move: (projT1_eq abs).
  move: {-}(e) => [= e1 ].
  case: _ / e1 in e *.
  rewrite [e]eq_axiomK /= => ys. 
  apply: bcongr_VCons.
    apply: Hf.
    apply: eqP.
  by have /= := H (existT _ n ys); case: peano_eqP => // p; rewrite [p]eq_axiomK /=.
by move=> tl; constructor=> abs; apply: e; apply: projT1_eq abs.
Qed. 


Lemma ok : forall (a : Type) (fa : a -> a -> bool) n pn (s1 : Coverage.vect a n), 
  vectR a (axiom a fa) n pn s1 -> axiom (Coverage.vect a n) (vect_eq a fa n) s1.
Proof.
move=> A f; apply: vect_induction.
  apply: bridge; exact: axiom_VNil.
move=> a Hf n nR xs /bridge2 IH; apply/bridge; exact: axiom_VCons.
Qed.


