From elpi Require Import elpi derive.projK derive.bcongr derive.isK derive.eq derive.eqK.

Elpi derive.projK prod.
Elpi derive.projK list.
Elpi derive.projK nat.
Elpi derive.projK bool.

Elpi derive.bcongr prod.
Elpi derive.bcongr list.
Elpi derive.bcongr nat.
Elpi derive.bcongr bool.

Elpi derive.isK prod.
Elpi derive.isK list.
Elpi derive.isK nat.
Elpi derive.isK bool.

Elpi derive.eq prod.
Elpi derive.eq list.
Elpi derive.eq nat.
Elpi derive.eq bool.

Elpi derive.eqK prod.

Check eq_axiom_pair : forall A fa B fb,
  forall a, axiom A fa a ->
  forall b, axiom B fb b ->
    axiom (A * B) (prod_eq A fa B fb) (a,b).

Elpi derive.eqK list.

Check eq_axiom_nil : forall A fa, axiom (list A) (list_eq A fa) (@nil A).

Check eq_axiom_cons : forall A fa,
  forall x, axiom A fa x ->
  forall xs, axiom (list A) (list_eq A fa) xs ->
    axiom (list A) (list_eq A fa) (cons x xs).
