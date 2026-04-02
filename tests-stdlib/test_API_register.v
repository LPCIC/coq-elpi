From elpi Require Import elpi.
From Stdlib Require Import Eqdep_dec.

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

Elpi Query lp:{{
  coq.env.scheme coq.register.scheme.eq_dec {{:gref T}} (some GR),
  coq.say "eq_dec scheme for T:" GR.
}}.

Elpi Query lp:{{
  coq.env.scheme coq.register.scheme.ind_dep {{:gref nat}} (some GR),
  coq.say "ind_dep scheme for nat:" GR.
}}.

Elpi Query lp:{{
  coq.env.scheme coq.register.scheme.rect_dep {{:gref nat}} (some GR),
  coq.say "rect_dep scheme for nat:" GR.
}}.

(* non-inductive gref returns none *)
Elpi Query lp:{{
  coq.env.scheme coq.register.scheme.ind_dep {{:gref T_dec}} none.
}}.
