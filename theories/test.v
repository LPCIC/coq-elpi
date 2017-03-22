From elpi Require Import elpi.

Elpi Init "./" "../elpi/".
Elpi Accumulate File "pervasives.elpi".
Elpi Accumulate File "coq_test.elpi".
Elpi Run "main.".

Elpi Accumulate " main2 X :- say nope, X = darling. ".
Elpi Run "main2 Res, say [my, Res]. ".