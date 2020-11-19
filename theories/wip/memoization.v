From elpi Require Import elpi.

(* Elpi does not feature tabling (memoization) but provides
   a very limited non-logical feature that can be used to store some (closed) data
   across backtracking. *)

Elpi Tactic auto2.
Elpi Accumulate lp:{{
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
  solve [] [G] [] :-
    repeat (any [exf, kon]) G [].

  % Here we cache proved goals
  type item term -> term -> item.
  pred memo-db o:safe.

  pred memo-lookup i:safe, i:term, o:term.
  memo-lookup Safe Ty P :- open_safe Safe L, std.exists L (i\ i = item Ty P).

  solve [str "memo"] [G] [] :-
    new_safe S,
    memo-db S => 
      repeat-memo (any[exf,kon]) G [].

  pred repeat-memo i:(goal -> list goal -> prop), i:goal, o:list goal.

  repeat-memo _ (goal _ P Ty _) [] :-
    memo-db DB, memo-lookup DB Ty P, coq.say "hit" Ty, !.

  repeat-memo T (goal _ P Ty _ as G) GS :-
    declare_constraint (rawevar->evar P Proof) [P],
    enter G T New, apply New (repeat-memo T) GS,
    if (GS = []) (memo-db DB, stash_in_safe DB (item Ty Proof)) true.

}}.
Elpi Typecheck.

Lemma l4 :
     (False \/ True)
  /\ (False \/ True)
  /\ (False \/ True)
  /\ (False \/ True)
  /\ (False \/ True)
  /\ (False \/ True)
  /\ (False \/ True)
.
Proof.
Time elpi auto2 memo. 
Qed.

