From elpi Require Import derive.induction derive.param1 derive.param1P.
From Coq Require Vector.

Elpi derive.induction nat.

Elpi derive.induction list.

Elpi derive.induction Vector.t.

Inductive nat1 := 
 | O (_ : bool)
 | S (_ : nat1 * (bool * list nat1)) (b : bool).

Elpi derive.param1 list.
Elpi derive.param1 prod.

Elpi derive.param1P list_param1.
Elpi derive.param1P prod_param1.
Elpi derive.induction nat1.
Check nat1_induction : forall P : nat1 -> Type,
       (forall b : bool, P (O b)) ->
       (forall a : nat1 * (bool * list nat1),
        prod_param1 nat1 P (bool * list nat1) 
         (prod_param1 bool (fun _ => True) (list nat1) (list_param1 nat1 P)) a ->
        forall b, P (S a b)) ->
       forall s : nat1, P s.

