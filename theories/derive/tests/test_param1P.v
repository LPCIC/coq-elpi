From elpi Require Import derive.param1 derive.param1P.

Elpi derive.param1 list.
Elpi derive.param1P is_list.

Check list_is_list :
  forall A P, (forall x : A, P x) -> forall l, is_list A P l.

Elpi derive.param1 prod.
Elpi derive.param1P is_prod.

Check prod_is_prod :
  forall A P, (forall x : A, P x) -> 
  forall B Q, (forall x : B, Q x) -> 
    forall p, is_prod A P B Q p.

Inductive xx := K (e : xx * xx).

Elpi derive.param1 xx.
Elpi derive.param1P is_xx.

Check is_xx : xx -> Type.
Check xx_is_xx : forall x : xx, is_xx x.