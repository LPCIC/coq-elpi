From elpi Require Import elpi.

Elpi Tactic data_passing.
Elpi Accumulate lp:{{

  pred dup i:string, i:term, i:goal, o:list sealed-goal.
  dup S T (goal C R Ty E I) GS :-
    std.zip {std.map C (x\r\x = decl r _ _)} {std.iota {std.length C} } Pos,
    std.lookup! Pos T N,
    G1 = goal C R Ty E [tactic-data S N|I],
    refine {{ _ lp:T }} G1 GS.

  pred clear i:string, i:goal, o:list sealed-goal.
  clear S (goal C _ _ E I as G) [seal G] :-
    std.mem! I (tactic-data S N),
    std.map C (x\r\x = decl r _ _) Names,
    std.zip {std.iota {std.length Names} } Names NamesPos,
    std.map-filter NamesPos (x\r\sigma Name P\x = pr P Name, not(P = N), r = Name) InScope,
    prune E InScope.

  solve [trm T] G GL :- name T,
    thenl [open (dup "copy" T),
           open (coq.ltac1.call "myidtac" [T]),
           open (clear "copy"),
           try (open (coq.ltac1.call "mycheck" [T])),
           ] (seal G) GL.

}}.
Elpi Typecheck.

Ltac myidtac X := idtac X.
Ltac mycheck X := let t := type of X in idtac t.

Goal forall z x : nat, True.
intros z x.
elpi data_passing (x).
Fail Check x.
Check z.
intro y.
Abort.