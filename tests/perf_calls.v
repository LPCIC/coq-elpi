From elpi Require Import elpi.

Definition x := 3.

Elpi Command perf.
Elpi Accumulate lp:{{

pred loop i:int, i:gref.
loop 0 _.
loop M GR :-
  N is M - 1,
  @local! => coq.arguments.set-implicit GR [[]],
  loop N GR.

main [int N] :-
  loop N {coq.locate "x"}.

}}.

Elpi Export perf.

Timeout 1 perf 3000.
