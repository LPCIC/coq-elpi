
From elpi Require Import elpi json.
From elpi Require json.tests.dummy. (* work around missing dune support for Extra Dependency *)

Elpi Command test.
Elpi Accumulate lp:{{ accumulate "elpi.json/all". }}.
Fail Elpi Query lp:{{
  std.assert-ok! (json.from_file "foo.json" X) "json"
}}.

From elpi.json.tests Extra Dependency "test.json" as json_test_file.


Elpi Query lp:{{
  coq.extra-dep "json_test_file" (some Path),
  std.assert-ok! (json.from_file Path X) "json",
  coq.say X,
  std.assert! ( X = json.assoc [pr "address" A| _]) "json",
  std.assert! ( A = json.assoc [pr "city" (json.string "New York")| _]) "json",
  Path1 is Path ^ ".out",
  std.assert-ok! (json.to_file Path1 X) "json"
}}.



(* the Elpi package json alone, with no Rocq wrapper *)
Elpi Command test_bare.
Elpi Accumulate lp:{{ accumulate "+json". }}.
Elpi Query lp:{{
  json.from_string "{ \"a\": [1, true] }" J ok,
  std.assert! (J = json.assoc [pr "a" (json.list [json.int 1, json.bool tt])]) "json",
  json.to_string J S ok,
  coq.say S
}}.
