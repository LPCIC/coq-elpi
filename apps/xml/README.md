Binding to xml-light
====================

This Rocq-Elpi plugin gives access to xml files.

```bash
opam install rocq-elpi-xml # pulls in xml-light
```

Then you can access the APIs in [doc/xml.elpi](doc/xml.elpi) this way:

```coq
From elpi Require Import elpi xml.

From elpi.xml.tests Extra Dependency "test.xml" as xml_test_file.

Elpi Command hello_xml.
Elpi Accumulate Plugin "xml.elpi".
Elpi Accumulate lp:{{
  main [str D] :-
    std.assert-ok! (coq.extra-dep->xml D X) "bad file",
    coq.say "xml AST:" X,
    coq.xml->string X S,
    coq.say "pretty:" S,
    coq.string->xml S X',
    coq.say "xml AST:" X',
    std.assert! (X = X') "this would be bad".
}}.
Elpi Export hello_xml.

hello_xml "xml_test_file".
```

Note: At the time of writing `rocq_makefile` fully supports this directive and
considers `<file>` as a dependency of the `.v` file. Dune does not yet
support this. For a workaround see the [tests/](tests-plugin/) directory.

