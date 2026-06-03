
From elpi Require Import elpi ext.
From elpi Require ext.tests.dummy.

Elpi Command test.
Elpi Accumulate Plugin "ext.elpi".
Elpi Accumulate  lp:{{
  pred encode term -> mynat.
  encode {{0}} myzero.
  encode {{S lp:X}} (mysucc Y) :- encode X Y.
}}.

Elpi Query  lp:{{
  encode {{0}} X,
  add1 X Z.
}}.
