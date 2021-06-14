From elpi Require Import elpi.

(* Elpi does not feature tabling (memoization) but provides
   a very limited non-logical feature that can be used to store some (closed) data
   across backtracking. *)

Elpi Tactic auto2.
Elpi Accumulate lp:{{
  % Ex falso
  pred exf i:goal, o:list sealed-goal.
  exf (goal Ctx _ Ty _ _ as G) [] :-
    std.exists Ctx (x\ sigma w\ x = decl V w {{False}}),
    refine {{ match lp:V in False return lp:Ty with end }} G [].
 
  % Constructor
  pred kon i:goal, o:list sealed-goal.
  kon (goal _ _ Ty _ _ as G) GS :-
    coq.safe-dest-app Ty (global (indt GR)) _,
    coq.env.indt GR _ _ _ _ Ks Kt,
    std.exists2 Ks Kt (k\ t\
      coq.saturate t (global (indc k)) P,
      refine P G GS).

  % entry point; we assert no goals are left
  solve (goal _ _ _ _ [] as G) [] :-
    coq.ltac.repeat (coq.ltac.or [coq.ltac.open exf, coq.ltac.open kon]) (seal G) [].

  % Here we cache proved goals
  type item term -> term -> item.
  pred memo-db o:safe.

  pred memo-lookup i:safe, i:term, o:term.
  memo-lookup Safe Ty P :- open_safe Safe L, std.exists L (i\ i = item Ty P).

  solve (goal _ _ _ _ [str "memo"] as G) [] :-
    new_safe S,
    memo-db S => 
      repeat-memo (coq.ltac.or[coq.ltac.open exf, coq.ltac.open kon]) G [].

  pred repeat-memo i:tactic, i:goal, o:list sealed-goal.

  repeat-memo _ (goal _ _ Ty P _) [] :-
    memo-db DB, memo-lookup DB Ty P, coq.say "hit" Ty, !.

  repeat-memo T (goal _ _ Ty Proof _ as G) GS :-
    T (seal G) New, coq.ltac.all (coq.ltac.open (repeat-memo T)) New GS,
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

