From elpi Require Import elpi xml.

From elpi.xml.tests Extra Dependency "test.xml" as xml_test_file.

Elpi Command hello_xml.
Elpi Accumulate Plugin "xml.elpi".
Elpi Accumulate lp:{{
  main [str D] :-
    std.assert-ok! (coq.extra-dep->xml D J) "bad file",
    coq.say "xml AST:" J,
    coq.xml->string J S,
    coq.say "pretty:" S,
    coq.string->xml S J',
    coq.say "xml AST:" J',
    std.assert! (J = J') "this would be bad".
}}.
Elpi Export hello_xml.

hello_xml "xml_test_file".
