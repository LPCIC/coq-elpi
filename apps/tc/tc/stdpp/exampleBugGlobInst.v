From elpi.apps.tc Require Import compiler.
From Coq Require Export Setoid.

Generalizable All Variables.

Class Inj {A B} (R : relation A) (S : relation B) (f : A -> B) : Prop :=
  inj x y : S (f x) (f y) -> R x y.

Section testInj.
  Context {A : Type}.
  Global Instance xxx : Inj eq eq (@id A). Admitted.
  Elpi add_instances Inj.
  Elpi Print TC_check.
End testInj.
Elpi Print TC_check.

Print Instances Inj.
Elpi print_instances.