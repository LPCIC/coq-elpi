From elpi Require Import elpi.

From myExtension Require Import Loader.
From myExtension.lib Extra Dependency "my-extension-elpi-code.elpi" as myExtensionLib.

Elpi Command test.
Elpi Accumulate Plugin "myExtension.elpi".
Elpi Accumulate File myExtensionLib.
Elpi Accumulate  lp:{{

  func encode term -> myType.
  encode {{lp:X + lp:Y}} (sumof X1 Y1) :- encode X X1, encode Y Y1, !.
  encode T (constant N) :- nat2int T N, !.
  encode T _ :- coq.error "This Rocq test does not fit myType" T.

  func decode myType -> term.
  decode (constant N) T :- int2nat N T, !.
  decode T _ :- coq.error "Not in normal form" T.
}}.

Elpi Query  lp:{{
  encode {{2 + 3}} X,

  compute X Z, 

  decode Z {{ 5 }}.
}}.