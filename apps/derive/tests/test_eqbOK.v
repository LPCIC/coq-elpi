From elpi.apps Require Import derive.eqbOK.

From elpi.apps.derive.tests Require Import test_derive_stdlib test_eqb test_eqbcorrect.

Import test_derive_stdlib.Coverage 
       test_eqb.Coverage
       test_eqbcorrect.Coverage.

Module Coverage.

Elpi derive.eqbOK peano. 

End Coverage.

Import Coverage.

Check peano_eqb_OK : forall n m, reflect (n = m) (peano_eqb n m).
