Binding to xml-light
====================

This Rocq-Elpi plugin gives access to xml files.

```bash
opam install rocq-elpi-xml # pulls in xml-light
```

Then you can access the APIs in [doc/xml.elpi](doc/xml.elpi) this way:

```coq
From elpi Require Import elpi xml.

(* Data you want to read from disk *)
From yourproject Extra Dependency "data.xml" as data.


Elpi Command read_xml.
Elpi Accumulate Plugin "xml.elpi". (* loads xml-light bindings *)
Elpi Accumulate lp:{{
main [str Dep] :-
  std.assert-ok! (coq.extra-dep->xml Dep X) "xml",
  coq.say "xml data:" X, % as an Elpi syntax tree
  coq.say "pretty printed:" {coq.xml->string X},
  std.assert! (X =
    xml.assoc [ % keys are sorted for us
      pr "first_name" (xml.string "John"),
      pr "is_alive"   (xml.bool tt), 
      pr "last_name"  (xml.string "Smith")])
   "not my data".
}}.

Elpi read_xml data. (* data is the name of the Extra Dependency *)
```

Note: At the time of writing `rocq_makefile` fully supports this directive and
considers `<file>` as a dependency of the `.v` file. Dune does not yet
support this. For a workaround see the [tests/](tests-plugin/) directory.

