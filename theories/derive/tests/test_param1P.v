From elpi Require Import derive.param1 derive.param1P.

Elpi derive.param1 list.
Elpi derive.param1P listR.

Check listRP :
  forall A P, (forall x : A, P x) -> forall l, listR A P l.

Elpi derive.param1 prod.
Elpi derive.param1P prodR.

Check prodRP :
  forall A P, (forall x : A, P x) -> 
  forall B Q, (forall x : B, Q x) -> 
    forall p, prodR A P B Q p.

Inductive xx := K (e : xx * xx).

Elpi derive.param1 xx.
Elpi derive.param1P xxR.

Check xxR : xx -> Type.
Check xxRP : forall x : xx, xxR x.