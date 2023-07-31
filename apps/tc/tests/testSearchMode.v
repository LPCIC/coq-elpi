From elpi Require Import compiler.
Unset TC_NameFullPath.
Elpi Debug "simple-compiler".

Elpi Override TC TC_solver All.

Class A (T : Set) := f : T -> T.
Elpi AddClasses deterministic A.

Global Instance A1 : A bool := {f x := x}.
Global Instance A2 `(A bool) : A (bool * bool) := 
  {f x := x}.
Global Instance A3 `(A nat) : A (bool * bool) := 
  {f x := x}.
Elpi AddAllInstances.

Goal A (bool * bool). Fail apply _. Abort.
