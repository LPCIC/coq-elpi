Binding to Yojson
=================

This Rocq-Elpi plugin gives access to json files.

```bash
opam install rocq-elpi-json # pulls in yojson
```

Then you can access the APIs in [doc/json.elpi](doc/json.elpi) this way:

```coq
From elpi Require Import elpi json.

(* Data you want to read from disk *)
From yourproject Extra Dependency "data.json" as data.


Elpi Command read_json.
Elpi Accumulate Plugin "json.elpi". (* loads yojson bindings *)
Elpi Accumulate lp:{{
main [str Dep] :-
  std.assert-ok! (coq.extra-dep->json Dep X) "json",
  coq.say "json data:" X, % as an Elpi syntax tree
  coq.say "pretty printed:" {coq.json->string X},
  std.assert! (X =
    json.assoc [ % keys are sorted for us
      pr "first_name" (json.string "John"),
      pr "is_alive"   (json.bool tt), 
      pr "last_name"  (json.string "Smith")])
   "not my data".
}}.

Elpi read_json data. (* data is the name of the Extra Dependency *)
```

Note: At the time of writing `rocq_makefile` fully supports this directive and
considers `<file>` as a dependency of the `.v` file. Dune does not yet
support this. For a workaround see the [tests/](tests/) directory.

