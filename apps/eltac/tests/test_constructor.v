From elpi.apps Require Import eltac.constructor.

Lemma test1 : 1 = 1.
Proof.
eltac.constructor.
Qed.

Example test_constructor : Type -> True * Type.
Proof.
intro x.
eltac.constructor.
- eltac.constructor.
- try eltac.constructor.
  assumption.
Qed.

