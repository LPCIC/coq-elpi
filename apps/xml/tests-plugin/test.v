
From elpi Require Import elpi xml.
From elpi Require xml.tests.dummy. (* work around missing dune support for Extra Dependency *)

Elpi Command test.
Elpi Accumulate Plugin "xml.elpi".
Fail Elpi Query lp:{{
  std.assert-ok! (xml.parse_file "foo.xml" X) "xml"
}}.

From elpi.xml.tests Extra Dependency "test.xml" as xml_test_file.


Elpi Query lp:{{
  coq.extra-dep "xml_test_file" (some Path),
  std.assert-ok! (xml.parse_file Path X) "xml",
  coq.say X,
  std.assert! ( X = xml.element "message" [] [A]) "xml",
  std.assert! ( A = xml.element "warning" [pr "level" "2", pr "zlevel" "2"] [xml.pcdata _]) "xml"
}}.


