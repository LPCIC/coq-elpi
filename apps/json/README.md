Binding to Yojson
=================

This Rocq-Elpi plugin gives access to json files.

```bash
opam install rocq-elpi-json # pulls in yojson
```

Then you can access the APIs in [doc/json.elpi](doc/json.elpi) this way:

```coq
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
```

Note: At the time of writing `rocq_makefile` fully supports this directive and
considers `<file>` as a dependency of the `.v` file. Dune does not yet
support this. For a workaround see the [tests/](tests-plugin/) directory.

