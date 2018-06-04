From elpi Require Import derive.param1 derive.map derive.induction derive.constsimplifier.

Elpi derive.param1 nat.
Elpi derive.param1P natR.
Elpi derive.induction nat.
Elpi derive.constsimplifier nat nat_ind.

Check nat_ind : forall P, P 0 -> (forall x, P x -> P (S x)) -> forall n, P n.

Elpi derive.param1 list.
Elpi derive.param1P listR.
Elpi derive.map listR.
Elpi derive.induction list. 

Elpi derive.constsimplifier list list_ind.

Check list_ind :
  forall (A : Type) (P : list A -> Type),
    P nil ->
    (forall H : A, forall H0 : list A, P H0 -> P (H :: H0)%list) -> forall x : list A, P x.

Inductive dlist A := dnil | dcons (a : A * nat) (l : dlist A).

Elpi derive.param1 prod.
Elpi derive.param1P prodR.
Elpi derive.map prodR.
Elpi derive.map natR.

Elpi derive.param1 dlist.
Elpi derive.param1P dlistR.

Elpi derive.induction dlist.
Elpi derive.constsimplifier dlist dlist_ind2.

Check dlist_induction :
  forall (A : Type) (PA : A -> Type) (P : dlist A -> Type),
  P (dnil A) ->
  (forall a : A * nat,
   prodR A PA nat natR a ->
   forall l : dlist A, P l -> P (dcons A a l)) -> forall x : dlist A, dlistR A PA x -> P x.

Check dlist_ind2 :
   forall (A : Type) (P : dlist A -> Type),
       P (dnil A) ->
       (forall a : A * nat, forall l : dlist A, P l -> P (dcons A a l)) ->
       forall x : dlist A, P x.

