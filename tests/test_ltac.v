From elpi Require Import elpi.

Elpi Tactic data_passing.
Elpi Accumulate lp:{{
  shorten coq.ltac.{ open , thenl , set-goal-arguments }.

  pred dup i:goal, o:list sealed-goal.
  dup (goal _ _ _ _ [trm T] as G) GS :-
    refine {{ _ lp:T }} G GL,
    std.map GL (set-goal-arguments [trm T] G) GS. % passing an argument to subgoals
    

  pred clear i:goal, o:list sealed-goal.
  clear (goal C _ _ E [trm T]) _ :-
    std.map C (x\r\x = decl r _ _) Names,
    std.filter Names (x\not (x = T)) InScope,
    prune E InScope.

  solve (goal _ _ _ _ [trm T] as G) GL :- name T,
    thenl [open dup, open clear] (seal G) GL.

}}.


Goal forall z x : nat, True.
intros z x.
elpi data_passing (x).
Fail Check x.
Check z.
intro y.
Abort.


(* Abstract *)

Ltac horror := abstract (exact I).

Elpi Command define_it.
Elpi Accumulate lp:{{
  main [] :-
    coq.elaborate-skeleton _ {{ True }} Bo ok,
    coq.ltac.collect-goals Bo [SealedGoal] [],
    coq.ltac.open (coq.ltac.call "horror" []) SealedGoal [],
    coq.locate "elpi_subproof" _,
    coq.env.add-const "it" Bo _ @transparent! C_.

}}.

Elpi define_it.

Print it.
About it.

Print elpi_subproof.
About elpi_subproof.

Print Assumptions it.


Elpi Tactic test_dep.
Elpi Accumulate lp:{{
  solve (goal _ _ {{ _ -> _ }} _ _) _.
}}.

Goal nat -> nat.
elpi test_dep.
Abort.

Goal forall T : Type, T -> T.
Fail elpi test_dep.
intro T.
elpi test_dep.
Abort.



Elpi Tactic barendregt.
Elpi Accumulate lp:{{
  solve (goal _ _ Ty _ Args as G) GL :-
    coq.say Ty,
    (pi N N' T F ID ID1\
      copy (fun N T F) (fun N' T1 F1) :- !,
        coq.name->id N ID,
        coq.ltac.fresh-id ID T ID1,
        if (Args = []) true (std.assert! (ID = ID1) "collision"),
        coq.id->name ID1 N',
        copy T T1,
        @pi-decl N T x\ copy (F x) (F1 x)) =>
    copy Ty Ty',
    refine {{ _ : lp:Ty' }} G GL.
}}.

Axiom map : (nat -> nat) -> nat.
Lemma test x : map (fun x => x + 1) = x.
Proof.
Fail elpi barendregt True.
elpi barendregt.
elpi barendregt True.
Abort.
