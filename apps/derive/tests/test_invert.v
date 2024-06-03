From elpi.apps Require Import derive.invert.

Inductive test A : bool -> Type :=
  K1 : test true
| K2 : forall x, A -> test (negb x) -> test (negb (negb x)).

Elpi derive.invert test.

Redirect "tmp" Check test_inv : Type -> bool -> Type.
Redirect "tmp" Check K1_inv : forall A b, b = true -> test_inv A b.
Redirect "tmp" Check K2_inv : forall A b, forall x, A -> test_inv A (negb x) -> b = negb (negb x) -> test_inv A b.

Inductive listR A PA : list A -> Type :=
  | nilR : listR (@nil A)
  | consR : forall a : A, PA a -> forall xs : list A, listR xs -> listR (cons a xs).

Elpi derive.invert listR.
Print listR_inv.