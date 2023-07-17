From elpi Require Import compiler.
Elpi Debug "simple-compiler".
Set AddModes.

Class A (S : Type) (T : Type).
Class B (S : Type) (T : Type).
Class C (S : Type).

Global Hint Mode A + - : typeclass_instances.
Global Hint Mode B - + : typeclass_instances.

Global Instance A1 : A nat nat. Admitted.
Global Instance B1 : B nat nat. Admitted.


Global Instance C1 {S T : Type} `{A T S, B S T} : C bool. Admitted.

Elpi AddAllClasses. 
Elpi AddAllInstances.
Elpi Override TC TC_solver All.

(* Here should give an error of cyclic dependencies *)
Goal C bool.
  apply _.
Qed.