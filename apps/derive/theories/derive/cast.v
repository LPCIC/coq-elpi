(* Generates (once and forall) cast operators (trasport).

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi.apps.derive.elpi Extra Dependency "cast.elpi" as cast.
   
From elpi Require Export elpi.

Elpi Db derive.cast.db lp:{{ func cast-db int -> term. }}.


Elpi Command derive.cast.
Elpi Accumulate Db derive.cast.db.
Elpi Accumulate File cast.
Elpi Accumulate  lp:{{

main [int N] :-
  derive.cast.main N.

}}.



Elpi derive.cast 2.
Elpi derive.cast 3.
Elpi derive.cast 4.
Elpi derive.cast 5.
Elpi derive.cast 6.
Elpi derive.cast 7.
