From elpi Require Import derive.param1 derive.induction derive.constsimplifier.

Elpi derive.induction list.
Elpi derive.constsimplifier list_induction list_ind.

Check list_ind :
  forall (A : Type) (P : list A -> Type),
    P nil ->
    (forall H : A, forall H0 : list A, P H0 -> P (H :: H0)%list) -> forall x : list A, P x.

Inductive dlist A := dnil | dcons (a : A * nat) (l : dlist A).

Elpi derive.param1 prod.
Elpi derive.param1 nat.
Elpi derive.param1P prodR.
Elpi derive.param1P natR.

Module XX.
Elpi derive.induction dlist.
Elpi derive.constsimplifier dlist_induction dlist_ind.
End XX. 

Check XX.dlist_induction :
  forall (A : Type) (P : dlist A -> Type),
  P (dnil A) ->
  (forall a : A * nat,
   prodR A (UnitPred A) nat natR a ->
   forall l : dlist A, P l -> P (dcons A a l)) -> forall x : dlist A, P x.

Check XX.dlist_ind :
   forall (A : Type) (P : dlist A -> Type),
       P (dnil A) ->
       (forall a : A * nat, forall l : dlist A, P l -> P (dcons A a l)) ->
       forall x : dlist A, P x.

