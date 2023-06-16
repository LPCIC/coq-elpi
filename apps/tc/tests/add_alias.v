From elpi Require Import compiler.
Elpi Override TC TC_solver All.
Elpi Debug "use-alias".

Class foo (A : Type) := f : Type.

Global Instance fooNat : foo nat := {f := nat}.
Global Instance fooBool : foo bool := {f := bool}.

Elpi AddInstances foo.

Definition nat' := nat.


Goal foo nat. apply _. Qed.
Goal foo bool. apply _. Qed.
Goal foo nat'. Fail apply _. Abort.

Module A.
  Elpi Accumulate TC_solver lp:{{
    alias {{nat'}} {{nat}}.
  }}.
  Goal foo nat'. apply _. Qed.
End A.

Definition nat'' := nat'.

Elpi AddAlias (nat'') (nat').
Goal foo nat''. apply _. Qed.
