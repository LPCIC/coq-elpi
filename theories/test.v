From elpi Require Import elpi.

Elpi Init "./" "../elpi/".
Elpi Accumulate File "pervasives.elpi".
Elpi Accumulate File "coq_test.elpi".
Elpi Run "main.".

Elpi Accumulate " main2 X :- say nope, X = darling. ".
Elpi Run "main2 Res, say [my, Res]. ".

Elpi Run "$locate ""nat"" X, say X. ".
Elpi Run "$locate ""S"" X, say X. ".
Elpi Run "$locate ""O"" X, say X. ".
Elpi Run "$locate ""S"" S,
          $locate ""O"" O,
          T = (app [S, app [S, O]]),
          say T,
          $coq-typecheck T TY,
          say TY,
          $coq-typecheck S STY,
          say STY,
          $coq-typecheck (lam ""foo"" TY x\app [S, x]) F,
          say F.
".

Elpi Run "
  $locate ""plus"" (const Plus),
  say Plus,
  $coq-env-const Plus Ty Bo,
  say Ty,
  say {pp Bo}.
".

