From elpi Require Import elpi.
From elpi_stdlib Require Import Eqdep_dec.

Inductive T : Type := a | b | f : T -> T.
Axiom T_dec : forall x y : T, {x = y} + {x <> y}.
Inductive V : T -> Type := V1 : V a | V2 : V b.
Inductive X : Type := B : forall (x : T), V x -> X.

Goal forall p q, B a p = B a q -> p = q.
intros p q H.
injection H.
apply (inj_pair2_eq_dec T T_dec).
Qed.


Elpi Command foo.

Elpi Query lp:{{

coq.register {{:gref T_dec}} (coq.register.scheme {{:gref T}} coq.register.scheme.eq_dec).

}}.

Goal forall p q, B a p = B a q -> p = q.
intros p q H.
injection H.
apply id.
Qed.
