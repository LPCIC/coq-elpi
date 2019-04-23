From elpi Require Import elpi.

(* Elpi does not feature tabling (memoization) but provides
   a non-logical feature that can be used to store some (closed) data
   across backtracking. *)

Elpi Tactic auto2 "
  % Ex falso
  pred exf i:goal, o:list goal.
  exf (goal Ctx _ Ty _ as G) [] :-
    std.exists Ctx (x\ x = decl V _ {{False}}),
    refine {{ match lp:V in False return lp:Ty with end }} G [].
 
  % Constructor
  pred kon i:goal, o:list goal.
  kon (goal _ _ Ty _ as G) GS :-
    safe-dest-app Ty (indt GR) _,
    coq.env.indt GR _ _ _ _ Ks Kt,
    std.exists2 Ks Kt (k\ t\
      saturate t k P,
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
  pred memo-db o:ctype ""safe"".

  pred memo-lookup i:@safe, i:term, o:term.
  memo-lookup Safe Ty P :- open_safe Safe L, std.exists L (i\ i = item Ty P).

  solve [str ""memo""] [G] [] :-
    new_safe S,
    memo-db S => 
      repeat-memo (any[exf,kon]) G [].

  pred repeat-memo i:(goal -> list goal -> prop), i:goal, o:list goal.

  repeat-memo _ (goal _ P Ty _) [] :-
    memo-db DB, memo-lookup DB Ty P, coq.say ""hit"" Ty, !.

  repeat-memo T (goal _ P Ty _ as G) GS :-
    enter G T New, apply New (repeat-memo T) GS,
    if (GS = []) (memo-db DB, stash_in_safe DB (item Ty P)) true.

".
Elpi Typecheck.

Lemma l4  (P : Prop) :
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

