From elpi Require Import elpi.

Elpi Db derive.castP.db " type castP-db int -> term -> prop. ".

Elpi Command derive.castP.
Elpi Accumulate Db derive.castP.db.
Elpi Accumulate File "derive/castP.elpi".
Elpi Accumulate  "

main [int N] :-
  derive-cast N.

".

Elpi Typecheck.

Elpi derive.castP 2.
Elpi derive.castP 3.
Elpi derive.castP 4.
Elpi derive.castP 5.
Elpi derive.castP 6.
Elpi derive.castP 7.
