From elpi Require Import elpi.

From elpi Require test_API.

Elpi Command declare.testX.
Elpi Accumulate Db global.db.
Elpi Accumulate lp:{{

main [str "mem", str I] :-
  std.assert! (declared I) "clause not present".
main [str "length", int I] :-
  std.findall (declared J_) L,
  std.assert! (std.length L I) "wrong number of clauses".

}}.
Elpi Typecheck.

Fail Elpi declare.testX "mem" "GLOBAL".
Elpi declare.testX "length" 0.

Import test_API. (* no dup *)

Elpi declare.test "mem" "GLOBAL".
Elpi declare.test "mem" "BOX".
Elpi declare.test "length" 2.

Fail Elpi declare.test "mem" "BOX.ClausesC".
Import Box.ClausesC.
Elpi declare.test "mem" "BOX.ClausesC".
Elpi declare.test "length" 3.

Elpi declare "library" "EXTRA".

(**  strategy *)
Definition x1 := 3.
Definition x2 := 3.
Strategy opaque [x2].
Definition x3 := 3.
Strategy expand [x3].

Elpi Command strategy.
Elpi Query lp:{{
  coq.locate "x1" (const X1),
  coq.locate "x2" (const X2),
  coq.locate "x3" (const X3),
  coq.strategy.get X1 (level 0),
  coq.strategy.get X2 opaque,
  coq.strategy.get X3 expand,
  coq.strategy.set [X3] (level 123),
  coq.strategy.get X3 (level 123).

}}.

Axiom P : nat -> Prop.

Elpi Command mode.
Elpi Query lp:{{
  coq.hints.add-mode {{:gref P }} "core" [mode-input],
  coq.hints.add-mode {{:gref P }} "core" [mode-ground],
  coq.hints.modes {{:gref P }} "core" M,
  std.assert! (M = [[mode-ground],[mode-input]]) "wrong modes"
}}.

Elpi Command pv.
Elpi Accumulate lp:{{

main [trm (primitive (uint63 P))] :- !, coq.say {coq.uint63->int P}.
main [trm (primitive (float64 P))] :- !, coq.say {coq.float64->float P}.
main X :- coq.error "not a primitive-value" X.

}}.
Elpi Typecheck.

From Coq Require Import PrimFloat Int63.

Open Scope int63_scope.

Elpi pv (1).
Fail Elpi pv (4611686018427387904). (* max_int + 1 *)

Open Scope float_scope.

Elpi pv (1.0).
