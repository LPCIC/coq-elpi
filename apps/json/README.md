Minimalistic binding to Yojson
==============================

This Rocq-Elpi plugin gives access to json files.

```bash
opam install rocq-elpi-json # pulls is yojson
```

Then you can access the APIs in [doc/json.elpi](doc/json.elpi) this way:

```coq
From elpi Require Import elpi json.

From yourproject Extra Dependency "data.json" as data.


Elpi Command read_json.
Elpi Accumulate Plugin "json.elpi".
Elpi Accumulate lp:{{
main [str Dep] :-
  std.assert-ok! (coq.extra-dep->json from_file Dep X) "json",
  coq.say X
}}.

Elpi read_json data.
```

Note: At the time of writing `rocq_makefile` fully supports this directive and
considers `<file>` as a dependency of the `.v` file. Dune does not yet
support this. For a workaround see the [tests/](tests/) directory.

