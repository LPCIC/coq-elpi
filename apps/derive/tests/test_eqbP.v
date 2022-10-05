From elpi.apps Require Import derive.eqbP.

From elpi.apps.derive.tests Require Import test_derive_stdlib test_eqb test_eqbcorrect test_eqbOK.

Import test_derive_stdlib.Coverage 
       test_eqb.Coverage
       test_eqbcorrect.Coverage
       test_eqbOK.Coverage.

Module Coverage.

Elpi derive.eqbP peano. 

End Coverage.

Import Coverage.

From mathcomp Require Import eqtype.

Check forall x : peano, x == x.

From elpi.apps Require Import derive.

#[only(eqbP), verbose] derive nat.

Check 1 == 0.

derive Inductive foo := | K.

Check K == K.