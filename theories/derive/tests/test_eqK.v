From elpi Require Import elpi derive.projK derive.bcongr derive.isK derive.eq derive.eqK.

From elpi Require Import
  test_derive_stdlib
  test_isK
  test_projK
  test_bcongr
  derive.tests.test_eq.

Module Coverage.

Elpi derive.eqK Coverage.empty.
Elpi derive.eqK Coverage.unit.
Elpi derive.eqK Coverage.peano.
Elpi derive.eqK Coverage.option.
Elpi derive.eqK Coverage.pair.
Elpi derive.eqK Coverage.seq.
Elpi derive.eqK Coverage.tree.
Fail Elpi derive.eqK Coverage.nest.
Fail Elpi derive.eqK Coverage.w.
Fail Elpi derive.eqK Coverage.vect.
Fail Elpi derive.eqK Coverage.dyn.
Fail Elpi derive.eqK Coverage.zeta.
Fail Elpi derive.eqK Coverage.beta.
Fail Elpi derive.eqK Coverage.iota.
Elpi derive.eqK Coverage.large.

End Coverage.





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
