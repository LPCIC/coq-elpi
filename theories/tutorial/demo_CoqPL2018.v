From elpi Require Import elpi.
From Coq Require Import Bool.

Elpi Command demo.

(**
  Let's build a few terms to get acquainted with how Coq
  terms are represented in Elpi. 
*)

(**
  A few type declarations (taken from coq-api.elpi):

type indt  @gref -> term. % nat, list, ...
type indc  @gref -> term. % O, S, nil, cons, ...
type const @gref -> term. % Nat.add, List.append, ...

type lam  @name -> term -> (term -> term) -> term. % fun x : t =>
type prod @name -> term -> (term -> term) -> term. % forall x : t,

type app   list term -> term.                   % app [hd|args]
type match term -> term -> list term -> term.   % match t p [branch])
type fix   @name -> int -> term -> (term -> term) -> term. % fix name rno ty bo

  where @name is a pretty print hint, @gref a global name.
  The former is printed as `name` while the latter as «name».

  The coq-locate predicate is similar to the Locate command of Coq.
*)

Elpi Query "
  coq-locate ""nat"" N
".


(** Now lets build
      forall x : nat, 0 <= x
    Note that "x\ ..." is the lambda abstraction of
    Elpi. E.g. the identity function is "x\ x" and
    Coq's identity function is (lam `x` (indt «nat») x\ x).
*)
Elpi Query "
  coq-locate ""nat"" N,
  coq-locate ""le"" L,
  coq-locate ""O"" Z,
  T = prod `x` N (x \ app [L, Z, x])  
".

(** We can use {{ quotations }} and
    lp:antiquotations in order to write
    terms in the concrete syntax of Coq *)

Elpi Query "
  T = {{ forall x : nat, 0 <= x }}
".

Elpi Query "
  T = {{ forall x : nat, lp:Z <= x }},
  coq-locate ""O"" Z
".

(** Let's pull from Coq's environment the
    recursive definition of plus *)

Elpi Query "
  coq-locate ""plus"" (const GR),
  coq-env-const GR Bo Ty. /*
  pp Ty NiceTy,
  pp Bo NiceBo. */
".

(** Let's pull from Coq's environment the
    declaration of nat *)

Elpi Query "
  coq-locate ""nat"" (indt GR),
  coq-env-indt GR Ind? Pno _ Arity KN KTy,
  map KTy pp NiceKTy.
".

(** --------------------------------------------- *)

(** Lets define a command generating a comparison
    function given an inductive data type declaration.

    We do it step by step.
 *)

Elpi Command eq1 "

 main [str X] :-
   coq-locate X (indt GR),
   derive-eq (indt GR) Cmp,
   Name is X ^""_cmp1"",
   coq-env-add-const Name Cmp _ _ _.

 derive-eq T R :-
   R = {{ fix f (n m : lp:T) {struct n} :
          lp:T -> lp:T -> bool :=
            lp:Bo f n m }},
   Bo = f\ n\ m\ {{true}}.
".
Elpi Typecheck.

Elpi eq1 nat. Print nat_cmp1.

(* Now let's pattern match on the first argument *)

Elpi Command eq2 "

 main [str X] :-
   coq-locate X (indt GR),
   derive-eq (indt GR) Cmp,
   Name is X ^""_cmp2"",
   coq-env-add-const Name Cmp _ _ _.

 derive-eq T R :-
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

  derive-eq-bo1 K _ _ _ {{ true }}.
 
".
Elpi Typecheck.

Elpi eq2 nat. Print nat_cmp2.

(* Now let's also match on the second one *)

Elpi Command eq3 "

 main [str X] :-
   coq-locate X (indt GR),
   derive-eq (indt GR) Cmp,
   Name is X ^""_cmp3"",
   coq-env-add-const Name Cmp _ _ _.

 derive-eq T R :-
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

  derive-eq-bo1 M GR Args K I V VT R :-
    build-match-skeleton M GR Args
      derive-eq-rty
      (derive-eq-bo2 K I V VT)
      R.

  derive-eq-bo2 K _ _ _ K _ _ _ {{ true }}.
  derive-eq-bo2 _ _ _ _ _ _ _ _ {{ false }}.
 
".
Elpi Typecheck.

Elpi eq3 nat. Print nat_cmp3.


Elpi Command eq4 "

 main [str X] :-
   coq-locate X (indt GR),
   derive-eq (indt GR) Cmp,
   Name is X ^""_cmp4"",
   coq-env-add-const Name Cmp _ _ _.

 type eq-db term -> term -> prop.

 derive-eq T R :-
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

  derive-eq-bo1 M GR Args K I V VT R :-
    build-match-skeleton M GR Args
      derive-eq-rty
      (derive-eq-bo2 K I V VT)
      R.

  derive-eq-bo2 K _ []     _ K _ []     []     {{ true }}.
  derive-eq-bo2 K _ [X|XS] _ K _ [Y|YS] [T|TS] {{ lp:CXY && lp:R }} :-
    eq-db T F, CXY = app [F,X,Y],
    derive-eq-bo2 K _ XS _ K _ YS TS R.

  derive-eq-bo2 _ _ _ _ _ _ _ _ {{ false }}.
 
".
Elpi Typecheck.

Elpi eq4 nat. Print nat_cmp4.

(* Some commands shipped with coq-elpi *)

From elpi Require Import derive.map derive.eq derive.param1.

Elpi derive.eq list.         About list_eq.
Elpi derive.map list.        About list_map.
Elpi derive.param1 list.     About list_param1.
Elpi derive.map list_param1. About list_param1_map.

(** -------------------------------------------------- *)

(** Tactics 

    The entry point of a tactic is called solve
    and the goal is made of a proof context, a type
    to inhabit and the corresponding evar to assign *)

Elpi Tactic id "
  solve _ [goal Ctx Ev Ty _] _ :-
    coq-say ""goal"" Ev ""is\n"" Ctx ""\n-------\n"" Ty.
". 
Elpi Typecheck.


Lemma l1 x y z (H : x < y) : y < z -> x < z.
Proof.
elpi id.
Abort.

(* Now we write "intro" in Curry-Howard style *)

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

(* Now let's write a little automation *)

Elpi Tactic auto "
  intro S G GS :- refine (lam S hole x\ hole) G GS.

  % Ex falso
  exf (goal Ctx _ Ty _ as G) [] :-
    exists Ctx (x\ x = decl V _ {{False}}),
    refine {{ match lp:V in False return lp:Ty with end }} G [].
 
  % Constructor
  kon (goal _ _ Ty _ as G) GS :-
    safe-dest-app Ty (indt GR) _,
    coq-env-indt GR _ _ _ _ Ks Kt,
    exists2 Ks Kt (k\ t\
      saturate t k P,
      refine P G GS).

  % a tactical like + but on a list of tactics
  any [T|_ ] G GS :- T G GS.
  any [_|TS] G GS :- any TS G GS.

  solve _ [G] [] :-
    repeat (any [exf, kon, intro `H`]) G [].

".
Elpi Typecheck.

Lemma l3 : forall P : Prop, (False -> P) /\ (False \/ True).
Proof.
elpi intro P.
elpi auto. 
Qed.


