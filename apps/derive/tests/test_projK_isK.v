From elpi.apps Require Import derive.isK derive.projK.

Set Universe Polymorphism.

Module ProjK_IsK.

Inductive Sum (A B : Type) := InL : A -> Sum A B | InR : B -> Sum A B.
Elpi derive Sum.
Redirect "tmp" Check Sum_isk_InL.
Redirect "tmp" Check Sum_isk_InR.
Redirect "tmp" Check Sum_getk_InL1.
Redirect "tmp" Check Sum_getk_InR1.

End ProjK_IsK.

Unset Universe Polymorphism.