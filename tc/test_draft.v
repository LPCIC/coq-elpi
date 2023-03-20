From elpi Require Import elpi.
From elpi.tc Require Import compiler.

Elpi hello "llo".

Elpi Program "ciao".
Elpi Query lp:{{
  coq.say "ciao".
}}.

Elpi Query lp:{{
  L = [1,2,3].
}}.