From elpi Require Import elpi.

Elpi Command test.
Elpi Accumulate lp:{{

main _ :-
  attributes A,
  coq.parse-attributes A [] Opts,
  Opts => (get-option "elpi.test" "yes",
           get-option "elpi.str" "some-string").

}}.
Elpi Typecheck.
Elpi Export test.

test.
