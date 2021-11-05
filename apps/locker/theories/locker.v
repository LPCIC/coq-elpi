(* Locking mechanisms.

   * mlock: module based locking.
     + hard locking (the body is really sealed) 
     - cannot be used inside sections

   * lock: opaque key based locking.
     + can be used everywhere
     - conversion may cross the lock (by congruence), while reduction will not

   license: GNU Lesser General Public License Version 2.1 or later
   ------------------------------------------------------------------------- *)

From Coq Require Import ssreflect.
From elpi Require Import elpi.

Elpi Command lock.
Elpi Accumulate File "elpi/locker.elpi".
Elpi Accumulate lp:{{
  main [const-decl ID (some Bo) Ty] :- !, locker.key-lock ID Bo Ty.
  main _ :- coq.error "Usage: lock Definition ...".
}}.
Elpi Typecheck.
Elpi Export lock.

Elpi Command mlock.
Elpi Accumulate File "elpi/locker.elpi".
Elpi Accumulate lp:{{
  main [const-decl ID (some Bo) Ty] :- !, locker.module-lock ID Bo Ty.
  main _ :- coq.error "Usage: mlock Definition ...".
}}.
Elpi Typecheck.
Elpi Export mlock.
