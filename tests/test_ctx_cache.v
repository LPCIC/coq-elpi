From elpi Require Import elpi.

Elpi Tactic perf.
Elpi Accumulate lp:{{

pred loop i:int, i:prop.
loop 0 _.
loop M P :-
  N is M - 1,
  P,
  loop N P.

solve (goal _ _ _ _ [str "cache", int N]) _ :- !,
  loop N (coq.unify-eq {{ 0 + 0 }} {{ 0 }} ok, @pi-decl `x` {{ bool }} x\ true).
solve (goal _ _ _ _ [str "nocache", int N]) _ :- !,
  loop N (@pi-decl `x` {{ bool }} x\ coq.unify-eq {{ 0 + 0 }} {{ 0 }} ok, true).


}}.
Elpi Typecheck.

Notation t := 
    (
        nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * nat *
        nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * nat *
        nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * nat *
        nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * nat *
        nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * nat *
        nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * nat *
        nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * nat *
        nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * nat    
    )%type.
Time Goal
forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : t),
forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : t),
forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : t),
forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : t),
forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : t),
True.
intros.
Optimize Heap.
Time elpi perf nocache 3000.
Optimize Heap.
Time elpi perf cache   3000.

trivial.
Qed.
