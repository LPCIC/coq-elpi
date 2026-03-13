From elpi Require Import elpi json.

From elpi.json.tests Extra Dependency "test.json" as json_test_file.

Elpi Command hello_json.
Elpi Accumulate Plugin "json.elpi".
Elpi Accumulate lp:{{
  main [str D] :-
    std.assert-ok! (coq.extra-dep->json D J) "bad file",
    coq.say "json AST:" J,
    coq.json->string J S,
    coq.say "pretty:" S,
    coq.string->json S J',
    coq.say "json AST:" J',
    std.assert! (J = J') "this would be bad".
}}.
Elpi Export hello_json.

hello_json "json_test_file".
