From elpi Require Import derive.param1 derive.param1P.

Elpi derive.param1 list _Forall.
Elpi derive.param1 prod _Forall.

Elpi derive.param1P list_Forall.
Elpi derive.param1P prod_Forall.

Check list_ForallP :
  forall A P, (forall x : A, P x) -> forall l, list_Forall A P l.
Check prod_ForallP :
  forall A P, (forall x : A, P x) -> 
  forall B Q, (forall x : B, Q x) -> 
    forall p, prod_Forall A P B Q p.
