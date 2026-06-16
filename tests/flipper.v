From elpi Require Import elpi.

From ext Require Import ext.

Elpi Command test.
(* loading the API created in ext.elpi *)
(* the name of this file is set in the target of doc/dune *)
Elpi Accumulate Plugin "ext.elpi".
Elpi Accumulate  lp:{{
  func int2nat int -> term.
  int2nat 0 {{0}} :- !.
  int2nat N {{S lp:R}} :- N > 0, N' is N - 1, int2nat N' R.

  func nat2int term -> int.
  nat2int {{0}} 0.
  nat2int {{S lp:R}} N :- nat2int R N', N is N' + 1.

  func is_nat term ->.
  is_nat {{0}}.
  is_nat {{S lp:_}}.

  func encode term -> mysumT.
  encode T (myC N) :- is_nat T, !, nat2int T N.
  encode {{lp:X + lp:Y}} (myA X1 Y1) :- encode X X1, encode Y Y1.

  func decode mysumT -> term.
  decode (myC N) T :- int2nat N T.
  decode (myA X Y) {{lp:X1 + lp:Y1}} :- decode X X1, decode Y Y1.
}}.

Elpi Query  lp:{{
  encode {{2 + 3}} X,
  % compute is the ocaml API defined in ext.ml
  compute X Z, 
  decode Z R.
}}.

(* Calling the command defined in theories *)
Elpi Query C lp:{{
  to_int z N, coq.say N.
}}.
