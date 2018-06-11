From elpi Require Import elpi derive.eq derive.projK derive.isK 
  derive.param1 derive.param1P derive.map
  derive.induction derive.isK derive.projK
  derive.cast derive.bcongr derive.eqK derive.eqOK.

Elpi derive.param1 prod.
Elpi derive.param1 list.
Elpi derive.param1 nat.
Elpi derive.param1 bool.

Elpi derive.param1P prodR.
Elpi derive.param1P listR.
Elpi derive.param1P natR.
Elpi derive.param1P boolR.

Elpi derive.map prodR.
Elpi derive.map listR.
Elpi derive.map natR.
Elpi derive.map boolR.

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

Elpi derive.induction nat.
Elpi derive.induction bool.
Elpi derive.induction list.
Elpi derive.induction prod.

Elpi derive.eq list. 
Elpi derive.eq prod.
Elpi derive.eq bool.
Elpi derive.eq nat.

Elpi derive.eqK list. 
Elpi derive.eqK prod.
Elpi derive.eqK bool.
Elpi derive.eqK nat.

(* tests *)

Elpi derive.eqOK bool.

Check bool_eqOK : forall x : bool, boolR x -> axiom bool bool_eq x.

Elpi derive.eqOK nat.

Check nat_eqOK : forall x : nat, natR x -> axiom nat nat_eq x.

Elpi derive.eqOK list.

Check list_eqOK : forall A fA (x : list A), listR A (axiom A fA) x -> axiom (list A) (list_eq A fA) x.

Elpi derive.eqOK prod.

Check prod_eqOK : forall A fA B fB (x : A * B), prodR A (axiom A fA) B (axiom B fB) x -> axiom (A*B) (prod_eq A fA B fB) x.

Inductive nat1 := 
 | O1 
 | S1 (_ : nat1 * (bool * list nat1)).

Elpi derive.param1 nat1.
Elpi derive.param1P nat1R.
Elpi derive.map nat1R.
Elpi derive.induction nat1.
Elpi derive.eq nat1.
Elpi derive.isK nat1.
Elpi derive.projK nat1.
Elpi derive.bcongr nat1.
Elpi derive.eqK nat1.

Elpi derive.eqOK nat1.

Check nat1_eqOK : forall x : nat1, nat1R x -> axiom nat1 nat1_eq x.
