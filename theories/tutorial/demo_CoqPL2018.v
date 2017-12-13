From elpi Require Import elpi.
From Coq Require Import Bool.

Elpi Command demo.

Elpi Query "
  coq-locate ""nat"" N
".

Elpi Query "
  coq-locate ""nat"" N,
  coq-locate ""le"" L,
  coq-locate ""O"" Z,
  T = prod `x` N (x \ app [L, Z, x])  % forall x : nat, 0 <= x
".

Elpi Query "
  T = {{ forall x : nat, 0 <= x }}
".

Elpi Query "
  T = {{ forall x : nat, lp:Z <= x }},
  coq-locate ""O"" Z
".

Elpi Query "
  coq-locate ""plus"" (const GR),
  coq-env-const GR Bo Ty,
  pp Ty NiceTy,
  pp Bo NiceBo.
".

Elpi Query "
  coq-locate ""list"" (indt GR),
  coq-env-indt GR Ind? Pno _ Arity KN KTy,
  map KTy pp NiceKTy.
".

Elpi Command eq1 "

 main [str X] :-
   coq-locate X (indt GR),
   coq-env-indt GR _ _ _ _ KN KTy,
   derive-eq (indt GR) KN KTy Cmp,
   Name is X ^""_cmp1"",
   coq-env-add-const Name Cmp _ _ _.

 derive-eq T _ _ R :-
   R = {{ fix f (n m : lp:T) {struct n} :
          lp:T -> lp:T -> bool :=
            lp:Bo f n m }},
   Bo = f\ n\ m\ {{true}}.
".
Elpi Typecheck.

Elpi eq1 nat. Print nat_cmp1.


Elpi Command eq2 "

 main [str X] :-
   coq-locate X (indt GR),
   coq-env-indt GR _ _ _ _ KN KTy,
   derive-eq (indt GR) KN KTy Cmp,
   Name is X ^""_cmp2"",
   coq-env-add-const Name Cmp _ _ _.

 derive-eq T _ _ R :-
   R = {{ fix f (n m : lp:T) {struct n} :
          lp:T -> lp:T -> bool :=
            lp:Bo f n m }},
   safe-dest-app T (indt GR) Args,
   pi f n m\
     build-match-skeleton n GR Args
       derive-eq-rty
       derive-eq-bo1
       (Bo f n m).

  derive-eq-rty _ _ _ {{ bool }}.

  derive-eq-bo1 _ _ _ _ {{ true }}.
 
".
Elpi Typecheck.

Elpi eq2 nat. Print nat_cmp2.



Elpi Command eq3 "

 main [str X] :-
   coq-locate X (indt GR),
   coq-env-indt GR _ _ _ _ KN KTy,
   derive-eq (indt GR) KN KTy Cmp,
   Name is X ^""_cmp3"",
   coq-env-add-const Name Cmp _ _ _.

 derive-eq T _ _ R :-
   R = {{ fix f (n m : lp:T) {struct n} :
          lp:T -> lp:T -> bool :=
            lp:Bo f n m }},
   safe-dest-app T (indt GR) Args,
   pi f n m\
     build-match-skeleton n GR Args
       derive-eq-rty
       (derive-eq-bo1 m GR Args)
       (Bo f n m).

  derive-eq-rty _ _ _ {{ bool }}.

  derive-eq-bo1 M GR Args K _ _ _ R :-
    build-match-skeleton M GR Args
      derive-eq-rty
      (derive-eq-bo2 K)
      R.

  derive-eq-bo2 K K _ _ _ {{ true }}.
  derive-eq-bo2 _ _ _ _ _ {{ false }}.
 
".
Elpi Typecheck.

Elpi eq3 nat. Print nat_cmp3.


Elpi Command eq4 "

 main [str X] :-
   coq-locate X (indt GR),
   coq-env-indt GR _ _ _ _ KN KTy,
   derive-eq (indt GR) KN KTy Cmp,
   Name is X ^""_cmp4"",
   coq-env-add-const Name Cmp _ _ _.

 type eq-db term -> term -> prop.

 derive-eq T _ _ R :-
   R = {{ fix f (n m : lp:T) {struct n} :
          lp:T -> lp:T -> bool :=
            lp:Bo f n m }},
   safe-dest-app T (indt GR) Args,
   pi f n m\
     eq-db T f =>
     build-match-skeleton n GR Args
       derive-eq-rty
       (derive-eq-bo1 m GR Args)
       (Bo f n m).

  derive-eq-rty _ _ _ {{ bool }}.

  derive-eq-bo1 M GR Args K _ A _ R :-
    build-match-skeleton M GR Args
      derive-eq-rty
      (derive-eq-bo2 K A)
      R.

  derive-eq-bo2 K [] K _ [] [] {{ true }}.
  derive-eq-bo2 K [X|XS] K _ [Y|YS] [T|TS] {{ lp:CXY && lp:R }} :-
    eq-db T F, CXY = app [F,X,Y],
    derive-eq-bo2 K XS K _ YS TS R.
  derive-eq-bo2 _ _ _ _ _ _ {{ false }}.
 
".
Elpi Typecheck.

Elpi eq4 nat. Print nat_cmp4.

Eval compute in (nat_cmp4 3 4, nat_cmp4 7 7).


From elpi Require Import derive.map derive.eq derive.param1.

Elpi derive.eq list.         About list_eq.
Elpi derive.map list.        About list_map.
Elpi derive.param1 list.     About list_param1.
Elpi derive.map list_param1. About list_param1_map.


Elpi Tactic id "
  solve _ [goal Ctx Ev Ty _] _ :-
    coq-say ""goal"" Ev ""is"" Ctx ""-------"" Ty.
". 
Elpi Typecheck.


Lemma l1 x y z (H : x < y) : y < z -> x < z.
Proof.
elpi id.
Abort.

Elpi Tactic intro "
  solve [str S] [G] GS :-
    coq-string->name S N,
    refine (lam N hole x\ hole) G GS.
".
Elpi Typecheck.

Lemma l2 x y z (H : x < y) : y < z -> x < z.
Proof.
elpi intro H1.
Abort.

Elpi Tactic auto "
  intro S G GS :- refine (lam S hole x\ hole) G GS.

  exf (goal Ctx _ Ty _ as G) [] :-
    exists Ctx (x\ x = decl V _ {{False}}),
    refine {{ match lp:V in False return lp:Ty with end }} G [].

  kon (goal _ _ Ty _ as G) GS :-
    safe-dest-app Ty (indt GR) _,
    coq-env-indt GR _ _ _ _ Ks Kt,
    exists2 Ks Kt (k\ t\
      saturate t k P,
      refine P G GS).

  any [T|_] G GS :- T G GS.
  any [_|TS] G GS :- any TS G GS.

  solve _ [G] [] :- repeat (any [exf, kon, intro `H`]) G [].
".
Elpi Typecheck.

Lemma l3 : forall P : Prop, (False -> P) /\ (False \/ True).
Proof.
elpi intro P.
elpi auto. 
Qed.



