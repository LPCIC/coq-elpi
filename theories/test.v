From elpi Require Import elpi.

Elpi Init "./" "../elpi/".
Elpi Accumulate File "pervasives.elpi".

Elpi Accumulate File "lp-lib.elpi".
Elpi Accumulate File "coq-lib.elpi".

Elpi Accumulate " main2 X :- say nope, X = darling. ".
Elpi Run "main2 Res, say [my, Res]. ".

Elpi Run "locate ""nat"" X, say X. ".
Elpi Run "locate ""S"" X, say X. ".
Elpi Run "locate ""O"" X, say X. ".
Elpi Run "locate ""S"" S,
          locate ""O"" O,
          T = (app [S, app [S, O]]),
          say T,
          coq-typecheck T TY,
          say TY,
          coq-typecheck S STY,
          say STY,
          coq-typecheck (lam ""foo"" TY x\app [S, x]) F,
          say F.
".

Elpi Run "
  locate ""plus"" (const PlusName),
  say PlusName,
  coq-env-const PlusName Bo Ty,
  say Ty,
  say {pp Bo},
  coq-typecheck Bo Ty.
".


Elpi Run "

  say {{ nat -> bool }},
  say {pp x\{{ nat -> lp:x }}},
  say {pp x\{{ nat -> lp:""x"" }}},
  {{ lp:"" say say "" }}
.

".

Fail Elpi Run " {{ lp:unknown }} ".

Elpi Run "

  say {{ forall x x, lp:"" {{ x }}  "" -> x }}.

".
Elpi Run "

  say {{ match (3,4) with (x,y) => x + y end }}.


".

Elpi Run "

  say {{ fix f (n : nat) (m:=0) { struct n } : nat := 
           match n with O => m | S k => f k end }}.

".

Require Import List.

Elpi Run "

  T = app [ {{ @cons }}, hole, {{ 0 }}, app [ {{ @nil }}, hole ] ],
  say T,
  coq-elaborate T T1 TTY,
  say T1,
  say TTY.

".

Elpi Run " say {{ cons }}. ".

