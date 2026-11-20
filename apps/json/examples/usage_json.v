From elpi Require Import elpi json.

From elpi.json.tests Extra Dependency "test.json" as json_test_file.

Elpi Command hello_json.
Elpi Accumulate lp:{{ accumulate "elpi.json/all". }}.
Elpi Accumulate lp:{{
  main [str D] :-
    std.assert-ok! (coq.extra-dep->json D J) "bad file",
    coq.say "json AST:" J,
    std.assert-ok! (json.pretty_to_string J S) "bad json",
    coq.say "pretty:" S,
    std.assert-ok! (json.from_string S J') "bad string",
    coq.say "json AST:" J',
    std.assert! (J = J') "this would be bad".
}}.
Elpi Export hello_json.

hello_json "json_test_file".
