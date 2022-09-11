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
solve (goal _ _ _ _ [str "deepcache", int N]) _ :- !,
  dloop N (coq.unify-eq {{ 0 + 0 }} {{ 0 }} ok, true).
solve (goal _ _ _ _ [str "nodeepcache", int N]) _ :- !,
  dloop N (@pi-decl `x` {{ bool }} x\coq.unify-eq {{ 0 + 0 }} {{ 0 }} ok, true).

pred dloop i:int, i:prop.
dloop 0 _.
dloop M P :-
  N is M - 1,
  P,
  @pi-decl `x` {{ bool }} x\ dloop N P.

}}.
Elpi Typecheck.

Elpi Command say.
Elpi Accumulate lp:{{ main [str X] :- coq.say X. }}.
Elpi Export say.

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
say "Huge context stup".
Time Goal
forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : t),
forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : t),
forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : t),
forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : t),
forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : t),
True.
intros.
say "----------------------".
say "## bench cache (same ctx)".
say "----------------------".
say "no cache, 3K".
Optimize Heap. Time elpi perf nocache 3000.
say "   cache, 3K".
Optimize Heap. Time elpi perf cache   3000.
say "----------------------".
say "## bench incremental cache (growing ctx)".
say "----------------------".
say "no cache, 1K".
Optimize Heap. Time elpi perf nodeepcache 1000.
say "no cache, 2K".
Optimize Heap. Time elpi perf nodeepcache 2000.
say "   cache, 3K".
Optimize Heap. Time elpi perf deepcache   3000.
say "   cache, 6K".
Optimize Heap. Time elpi perf deepcache   6000.
say "   cache, 9K".
Optimize Heap. Time elpi perf deepcache   9000.
say "----------------------".
trivial.
Qed.
