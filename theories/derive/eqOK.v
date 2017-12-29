From elpi Require Import elpi. (*
  derive.eq derive.projK derive.isK 
  derive.param1 derive.param1P derive.map.
From Coq Require Import Bool List ssreflect.

Elpi derive.param1 prod prodR.
Elpi derive.param1 list listR.
Elpi derive.param1P prodR.
Elpi derive.param1P listR.
Elpi derive.map prodR.
Elpi derive.map listR.

Inductive nat1 := 
 | O (_ : bool)
 | S (_ : nat1 * (bool * list nat1)) (b : bool).
About nat1_ind.
Definition nat1_induction
: forall P : nat1 -> Type,
       (forall b : bool, P (O b)) ->
       (forall a : nat1 * (bool * list nat1), forall b : bool,
        prodR nat1 P (bool * list nat1) 
         (prodR bool (fun _ => True) (list nat1) (listR nat1 P)) a ->
        P (S a b)) ->
       forall s : nat1, P s.
Proof.
move=> P fO fS; fix IH 1 => n.
refine match n as m in nat1 return P m with
  | O b => fO b
  | S p q => fS p q _
end.
apply: prodRP => [a | bl].
  apply: IH.
apply: prodRP => [b' | l].
  exact: I.
apply: listRP.
apply IH.
Qed.

Elpi derive.eq list. 
Elpi derive.eq prod.
Elpi derive.eq bool.
Elpi derive.eq nat1.

Definition axiom T eqb x := forall (y : T), reflect (x = y) (eqb x y).

Lemma reflect_eq_f1 T rT (f : T -> rT) x y (inj_f : forall x y, f x = f y -> x = y) b :
  reflect (x = y) b -> reflect (f x = f y) b.
Proof.
case=> [ -> | abs ]; first by constructor 1.
by constructor 2 => /inj_f .
Qed.

(*
Lemma reflect_eq_f2 T rT (f : T -> rT) x y 
   (inj_f : f x = f y -> x = y) b1 b2 :
  reflect (f = f) b1 ->
  reflect (x = y) b2 -> reflect (f x = f y) (b1 && b2).
Proof.
by case=> [ E1 | abs1 ]; case=> [ -> | abs2 ]; constructor => //; try move/inj_f.
Qed.
*)
Lemma reflect_eq_f2 T S rT (f : T -> S -> rT) x y a b 
   (inj_f1 : forall x y a b, f x a = f y b -> x = y)
   (inj_f2 : forall x y a b, f x a = f y b -> a = b)
    b1 b2 :
  reflect (x = y) b1 ->
  reflect (a = b) b2 -> reflect (f x a = f y b) (b1 && b2).
Proof.
case=> [ -> | abs1 ]; case=> [ -> | abs2 ]; constructor => //; first [ by move/inj_f1 | by move/inj_f2 ].
Qed.

Lemma list_eqOK A f :
  forall x (HA : listR A (axiom A f) x),
  axiom (list A) (list_eq A f) x.
Proof.
move=> l; elim => [|x Px xs Pxs IH] [|y ys].
- constructor 1; reflexivity.
- constructor 2 => ?; discriminate.
- constructor 2 => ?; discriminate.
- apply: reflect_eq_f2=> [????[]|????[]||] //.
Qed.

Lemma prod_eqOK A f B g :
  forall x (H : prodR A (axiom A f) B (axiom B g) x),
  axiom (A * B) (prod_eq A f B g) x.
Proof.
move=> x [a Ha b Hb] [w z].
apply: reflect_eq_f2 => [????[]|????[]||] //. 
Qed.

Lemma nat1_eqOK b x : axiom (nat1 b) (nat1_eq b) x.
Proof.
apply: (nat1_induction (axiom nat1 nat1_eq)) => [ | p IH] [ | q].
- constructor 1; reflexivity.
- constructor 2 => ?; discriminate.
- constructor 2 => ?; discriminate.
- apply: reflect_eq_f1.
  + by move=> ?? [E].
  + rewrite /=.
    apply: prod_eqOK.
    apply: prodR_map IH => // l Hl.
    apply: list_eqOK.  
    apply: listR_map Hl => //.
Qed.

*)

Elpi Command derive.eqOK.
Elpi Accumulate File "derive/eqOK.elpi".
Elpi Accumulate "
  main [str I] :- !,
    coq-locate I T,
    if (T = indt GR) (derive-eqOK GR) usage.
  main _ :- usage.

  usage :- coq-error ""Usage: derive.eqOK <inductive type name>"".
". 
