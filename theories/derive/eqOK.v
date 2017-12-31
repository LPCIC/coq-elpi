From elpi Require Import elpi
  derive.eq derive.projK derive.isK 
  derive.param1 derive.param1P derive.map
  derive.induction derive.isK derive.projK.

From Coq Require Import Bool List ssreflect.

Elpi derive.param1 prod.
Elpi derive.param1 list.
Elpi derive.param1P prod_param1.
Elpi derive.param1P list_param1.
Elpi derive.map prod_param1.
Elpi derive.map list_param1.

Inductive nat1 := 
 | O 
 | S (_ : nat1 * (bool * list nat1)).

Elpi derive.induction nat1.
Elpi derive.induction nat.
Elpi derive.induction bool.
Elpi derive.induction list.
Elpi derive.induction prod.

Elpi derive.eq list. 
Elpi derive.eq prod.
Elpi derive.eq bool.
Elpi derive.eq nat.
Elpi derive.eq nat1.

Elpi derive.isK bool.
Elpi derive.isK nat.
Elpi derive.isK list.
Module XX.
Elpi derive.isK nat1.
End XX.

Definition axiom T eqb x :=
  forall (y : T), reflect (x = y) (eqb x y).

Lemma reflect_eqf_last T rT (f : T -> rT) x y 
  (inj_f : forall x y, f x = f y -> x = y) b :
  reflect (x = y) b -> reflect (f x = f y) b.
Proof.
case=> [ -> | abs ]; first by constructor 1.
by constructor 2 => /inj_f .
Qed.

Lemma reflect_eq_f2 T S rT (f : T -> S -> rT) x y a b 
   (inj_f1 : forall x y a b, f x a = f y b -> x = y)
   (inj_f2 : forall x y a b, f x a = f y b -> a = b)
    b1 b2 :
  reflect (x = y) b1 ->
  reflect (a = b) b2 -> reflect (f x a = f y b) (b1 && b2).
Proof.
case=> [ -> | abs1 ]; case=> [ -> | abs2 ]; constructor => //; first [ by move/inj_f1 | by move/inj_f2 ].
Qed.

Lemma reflect_eq_fx T S rT (f : T -> S -> rT) x y a b 
   (inj_f1 : forall x y a b, f x a = f y b -> x = y)
    b1 b2 :
  reflect (x = y) b1 ->
  reflect (f x a = f x b) b2 -> reflect (f x a = f y b) (b1 && b2).
Proof.
case=> [ -> // | ] /= H.
case=> [ -> // | K ].
  by constructor=> /inj_f1.
by constructor=> /inj_f1.
Qed.

Axiom daemon : False.

Elpi Command derive.eqOK.
Elpi Accumulate Db derive.isK.db.
Elpi Accumulate File "ltac/discriminate.elpi".
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1P.db.
Elpi Accumulate Db derive.induction.db.
Elpi Accumulate File "derive/eqOK.elpi".
Elpi Accumulate "
  main [str I, str F] :- !,
    coq-locate I (indt GR),
    coq-locate F (const Cmp),
    derive-eqOK GR Cmp.
  main _ :- usage.

  usage :- coq-error ""Usage: derive.eqOK <inductive type name>"".
".
Elpi Typecheck.

Elpi derive.eqOK bool bool_eq.
Check bool_eqOK : forall x, axiom bool bool_eq x.


(*
Lemma nat_eqOK x : axiom nat nat_eq x.
Proof.
move: x; apply: nat_induction => [|x]. case.
  by constructor.
  by move=> x; constructor.
move=> IH; case.
  by constructor.
move=> y.
apply: reflect_eq_fx.
*)

Elpi derive.eqOK nat nat_eq.
Print nat_eqOK.

(*
Lemma bool_eqOK x : axiom bool bool_eq x.
Proof.
elim: x => -[|]; by constructor.
Qed.

Lemma list_eqOK A f :
  forall x (HA : list_param1 A (axiom A f) x),
  axiom (list A) (list_eq A f) x.
Proof.
move=> l; elim => [|x Px xs Pxs IH] [|y ys].
- constructor 1; reflexivity.
- constructor 2 => ?; discriminate.
- constructor 2 => ?; discriminate.
- apply: reflect_eq_f2=> [????[]|????[]||] //.
Qed.

Lemma prod_eqOK A f B g :
  forall x (H : prod_param1 A (axiom A f) B (axiom B g) x),
  axiom (A * B) (prod_eq A f B g) x.
Proof.
move=> x [a Ha b Hb] [w z].
apply: reflect_eq_f2 => [????[]|????[]||] //. 
Qed.

Lemma nat1_eqOK x : axiom nat1 nat1_eq x.
Proof.
apply: (nat1_induction (axiom nat1 nat1_eq)) => [ | a IH] [ | b ].
- constructor 1 => //.
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