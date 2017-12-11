Require Import elpi. (*
elpi.derive.eq elpi.derive.projK elpi.derive.isK elpi.derive.param1 derive.map.

Require Import Bool List ssreflect.


Elpi derive.map prod.
Elpi derive.map list.

Elpi derive.param1 prod prodR.
Elpi derive.param1 list listR.
Elpi derive.map prodR.
Elpi derive.map listR.


Lemma listRP A P (H : forall a: A, P a) : forall l, listR A P l.
Proof.
fix f 1 => - [| x xs].
  constructor 1. 
by constructor 2.
Defined.

Lemma prodRP A P (H1 : forall a: A, P a)  B Q (H2 : forall b: B, Q b) :
  forall x, prodR A P B Q x.
Proof.
fix f 1 => - [x y].
by constructor 1. 
Defined.

Inductive nat1 : Type := O : nat1 | S (_ : nat1 * list nat1).
Elpi derive.param1 nat1 nat1R.

Lemma nat1RP : forall n : nat1, nat1R n.
Proof.
fix IH 1 => n.
refine match n as w in nat1 return nat1R w
       with O => _ | S x => _ end.
refine nat1R_O.
refine (nat1R_S _ _).
refine (prodRP _ _ IH _ _ (listRP _ _ IH) _).
Defined.

Definition nat1R_ind_fixed
: forall P : nat1 -> Type,
       P O ->
       (forall H : nat1 * list nat1,
        prodR nat1 P (list nat1) (listR nat1 P) H -> P (S H)) ->
       forall s : nat1, nat1R s -> P s.
Proof.
move=> P fO fS; fix IH 2 => n nr.
refine 
match nr in nat1R m return P m with
| nat1R_O => fO
| nat1R_S s Ps => fS s _
end.
refine (prodR_map _ _ _ IH _ _ _ (listR_map _ _ _ IH) _ Ps).
Qed.

Definition nat1_induction P PO PS x :=
  nat1R_ind_fixed P PO PS x (nat1RP x).

Elpi derive.eq list.
Elpi derive.eq prod.
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

Lemma nat1_eqOK x : axiom nat1 nat1_eq x.
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
