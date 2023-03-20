From elpi Require Import elpi.

Elpi Command hello.
Elpi Accumulate lp:{{

  % main is, well, the entry point
  main Arguments :- coq.say "Hello" Arguments.

}}.
Elpi Typecheck.