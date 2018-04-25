(* Generates (once and forall) cast operators (trasport).

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Import elpi.

Elpi Db derive.cast.db " type cast-db int -> term -> prop. ".

Elpi Command derive.cast.
Elpi Accumulate Db derive.cast.db.
Elpi Accumulate File "derive/cast.elpi".
Elpi Accumulate  "

main [int N] :-
  derive.cast.main N.

".

Elpi Typecheck.

Elpi derive.cast 2.
Elpi derive.cast 3.
Elpi derive.cast 4.
Elpi derive.cast 5.
Elpi derive.cast 6.
Elpi derive.cast 7.
