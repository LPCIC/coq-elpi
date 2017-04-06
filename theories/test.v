From elpi Require Import elpi.

Elpi Init "./" "../elpi/".
Elpi Accumulate File "pervasives.elpi".

Elpi Accumulate File "lp-lib.elpi".
Elpi Accumulate File "coq-lib.elpi".

Elpi Accumulate " main2 X :- coq-say nope, X = darling. ".
Elpi Run "main2 Res, coq-say [my, Res]. ".

Elpi Run "coq-locate ""nat"" X, coq-say X. ".
Elpi Run "coq-locate ""S"" X, coq-say X. ".
Elpi Run "coq-locate ""O"" X, coq-say X. ".
Elpi Run "coq-locate ""S"" S,
          coq-locate ""O"" O,
          T = (app [S, app [S, O]]),
          coq-say T,
          coq-typecheck T TY,
          coq-say TY,
          coq-typecheck S STY,
          coq-say STY,
          coq-typecheck (lam ""foo"" TY x\app [S, x]) F,
          coq-say F.
".

Elpi Run "
  coq-locate ""plus"" (const PlusName),
  coq-say PlusName,
  coq-env-const PlusName Bo Ty,
  coq-say Ty,
  coq-say {pp Bo},
  coq-typecheck Bo Ty.
".


Elpi Run "

  coq-say {{ nat -> bool }},
  coq-say {pp x\{{ nat -> lp:x }}},
  coq-say {pp x\{{ nat -> lp:""x"" }}},
  {{ lp:"" coq-say say "" }}
.

".

Fail Elpi Run " {{ lp:unknown }} ".

Elpi Run "

  coq-say {{ forall x x, lp:"" {{ x }}  "" -> x }}.

".
Elpi Run "

  coq-say {{ match (3,4) with (x,y) => x + y end }}.


".

Elpi Run "

  coq-say {{ fix f (n : nat) (m:=0) { struct n } : nat := 
           match n with O => m | S k => f k end }}.

".

Require Import List.

Elpi Run "

  T = app [ {{ @cons }}, hole, {{ 0 }}, app [ {{ @nil }}, hole ] ],
  coq-say T,
  coq-elaborate T T1 TTY,
  coq-say T1,
  coq-say TTY.

".

Elpi Run " coq-say {{ cons }}. ".

