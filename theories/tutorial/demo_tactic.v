From elpi Require Import elpi.

(* Tactics 

    The entry point of a tactic is called solve
    and the goal is made of a proof context, a type
    to inhabit and the corresponding evar to assign *)

Elpi Tactic id "
  solve _ [goal Ctx Ev Ty _] _ :-
    coq.say ""goal"" Ev ""is\n"" Ctx ""\n-------\n"" Ty.
". 
Elpi Typecheck.


Lemma l0 x y z (H : x < y) : y < z -> x < z.
Proof.
elpi id.
Abort.

(* Things are wired up in such a way that assigning a
   "wrong" value to Ev fails *)

Elpi Tactic silly "
  solve _ [goal _ Ev _ _] _ :- Ev = {{true}}.
  solve _ [goal _ Ev _ _] _ :- Ev = {{3}}.
". 
Elpi Typecheck.

Lemma l1 : nat.
Proof.
elpi silly.
Show Proof.
Qed.

(* Now we write "intro" in Curry-Howard style *)

Elpi Tactic intro "
  solve [str S] [G] GS :-
    coq.string->name S N,
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
    coq.env.indt GR _ _ _ _ Ks Kt,
    exists2 Ks Kt (k\ t\
      saturate t k P,
      refine P G GS).

  % a tactical like + but on a list of tactics
  any [T|_ ] G GS :- T G GS.
  any [_|TS] G GS :- any TS G GS.

  % entry point; we assert no goals are left
  solve _ [G] [] :-
    repeat (any [exf, kon, intro `H`]) G [].

".
Elpi Typecheck.

Lemma l3 : forall P : Prop, (False -> P) /\ (False \/ True).
Proof.
elpi auto. 
Qed.



