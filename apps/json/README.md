Binding to Yojson
=================

This Rocq-Elpi app gives access to json files. It is a small Elpi wrapper,
[theories/all.elpi](theories/all.elpi), over the Elpi package `json` (the
findlib package `elpi-json`, Yojson bindings), whose plugin is loaded when a
program accumulates `"+json"`.

```bash
opam install rocq-elpi-json # pulls in elpi-json
```

Then you can access the APIs of `elpi-json` (`json.*`, see its
`json.builtins.elpi`) and the Rocq specific ones of the wrapper this way:

```coq
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
```

Note: At the time of writing `rocq_makefile` fully supports this directive and
considers `<file>` as a dependency of the `.v` file. Dune does not yet
support this. For a workaround see the [tests/](tests-plugin/) directory.

