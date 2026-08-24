From elpi.apps Require Import derive.derive derive.isK derive.projK.

Set Universe Polymorphism.

Module ProjK_IsK.

Inductive Sum (A B : Type) := InL : A -> Sum | InR : B -> Sum.
derive Sum.
Redirect "tmp" Check Sum_is_InL.
Redirect "tmp" Check Sum_is_InR.
Redirect "tmp" Check Sum_projInL1.
Redirect "tmp" Check Sum_projInR1.

End ProjK_IsK.

Unset Universe Polymorphism.