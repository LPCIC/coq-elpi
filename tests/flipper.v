
From elpi Require Import elpi ext.
From elpi Require ext.tests.dummy.

Elpi Command test.
Elpi Accumulate Plugin "ext.elpi".
Elpi Accumulate  lp:{{
  pred encode term -> mysumT.
  encode {{0}} (myC 0).
  encode {{S lp:X}} (myC N1) :- 
    encode X (myC N), N1 is N + 1.
  encode {{lp:X + lp:Y}} (myA X1 Y1) :- encode X X1, encode Y Y1.

  pred decode mysumT -> term.
  decode (myC 0) {{0}} :- !.
  decode (myC N1) {{S lp:X}} :- !,
    N2 is N1 - 1, decode (myC N2) X.
  decode (myA X1 Y1) {{lp:X + lp:Y}} :- decode X1 X, decode Y1 Y.
  decode A _ :- coq.error "A = " A.
}}.

Elpi Query  lp:{{
  encode {{2 + 3}} X,
 compute X Z, decode Z R.
}}.
