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
