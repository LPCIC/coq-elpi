From elpi Require Import elpi.

(* Tactics 

    The entry point of a tactic is called solve
    and the goal is made of a proof context, a type
    to inhabit and the corresponding evar to assign *)

Elpi Tactic id.
Elpi Accumulate lp:{{
  solve _ [goal Ctx Ev Ty _] _ :-
    coq.say "goal" Ev "is\n" Ctx "\n-------\n" Ty.
}}. 
Elpi Typecheck.


Lemma l0 x y z (H : x < y) : y < z -> x < z.
Proof.
elpi id.
Abort.

(* Things are wired up in such a way that assigning a
   "wrong" value to Ev fails *)

Elpi Tactic silly.
Elpi Accumulate lp:{{
  solve _ [goal _ Ev _ _] _ :- Ev = {{true}}.
  solve _ [goal _ Ev _ _] _ :- Ev = {{3}}.
}}. 
Elpi Typecheck.

Lemma l1 : nat.
Proof.
elpi silly.
Show Proof.
Qed.

(* Now we write "intro" in Curry-Howard style *)

Elpi Tactic intro.
Elpi Accumulate lp:{{
  solve [str S] [G] GS :-
    coq.string->name S N,
    refine (fun N Src_ Tgt_) G GS.
}}.
Elpi Typecheck.

Lemma l2 x y z (H : x < y) : y < z -> x < z.
Proof.
elpi intro H1.
Abort.

(* Now let's write a little automation *)

Elpi Tactic auto.
Elpi Accumulate lp:{{
  pred intro i:name, i:goal, o:list goal.
  intro S G GS :- refine (fun S Src_ Tgt_) G GS.

  % Ex falso
  pred exf i:goal, o:list goal.
  exf (goal Ctx _ Ty _ as G) [] :-
    std.exists Ctx (x\ sigma w\ x = decl V w {{False}}),
    refine {{ match lp:V in False return lp:Ty with end }} G [].
 
  % Constructor
  pred kon i:goal, o:list goal.
  kon (goal _ _ Ty _ as G) GS :-
    coq.safe-dest-app Ty (global (indt GR) UI) _,
    coq.env.indt GR UI _ _ _ _ Ks Kt,
    std.exists2 Ks Kt (k\ t\
      saturate t (global (indc k) UI) P,
      refine P G GS).

  % a tactical like + but on a list of tactics
  pred any i:list (goal -> list goal -> prop), i:goal, o:list goal.
  any [T|_ ] G GS :- T G GS.
  any [_|TS] G GS :- any TS G GS.

  % entry point; we assert no goals are left
  solve _ [G] [] :-
    repeat (any [exf, kon, intro `H`]) G [].

}}.
Elpi Typecheck.

Lemma l3 : forall P : Prop, (False -> P) /\ (False \/ True).
Proof.
elpi auto. 
Qed.



