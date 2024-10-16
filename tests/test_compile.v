From elpi Require Import elpi.

Elpi Command foo.
Elpi Accumulate lp:{{
  main _ :- coq.say "ok".
}}.

Set Debug "elpitime".
Elpi Compile foo.
Elpi foo.