From elpi Require Export elpi.

Elpi Tactic cycle.
Elpi Accumulate lp:{{

  pred read-arg i:sealed-goal, o:list argument.
  read-arg (nabla G) X :- pi x\ read-arg (G x) X.
  read-arg (seal (goal _ _ _ _ A)) A.

  pred cycle i:int, i:list sealed-goal, o:list sealed-goal.
  cycle N L PL :- N > 0,
    std.length L M,
    std.assert! (N < M) "not enough goals",
    std.split-at N L B A,
    std.append A B PL.
  cycle N L PL :- N < 0,
    std.length L M,
    N' is M + N,
    cycle N' L PL.

  msolve GL GS :-
    GL = [G|_],
    read-arg G [int N],
    if (N = 0) (GS = GL) (cycle N GL GS).

}}.

Elpi Typecheck.

Tactic Notation "eltac.cycle" int(n) := elpi cycle ltac_int:(n).
