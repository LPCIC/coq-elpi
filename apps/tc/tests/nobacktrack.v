From elpi.apps Require Import tc.

Elpi Debug "simple-compiler".
Unset TC_NameFullPath.

Module A.

  Class C (n : nat) := {}.
  Local Instance c_1 : C 1 | 10 := {}.
  Local Instance c_2 : C 2 | 1 := {}.

  Class D (n : nat) := {}.
  Local Instance d_1 : D 1 := {}.

  Class E (n : nat) := {}.
  Local Instance foo {n} : C n -> D n -> E n := {}.

  #[deterministic] Elpi AddClasses C.
  Elpi AddClasses D E.
  Elpi AddAllInstances.
  Elpi Override TC TC_solver All.

  Goal exists n, E n.
    eexists.
    Fail apply _.
  Abort.

End A.

Module B.

  Class A (T : Set) := f : T -> T.
  #[deterministic] Elpi AddClasses A.

  Global Instance A1 : A bool := {f x := x}.
  Global Instance A2 `(A bool) : A (bool * bool) := 
    {f x := x}.
  Global Instance A3 `(A nat) : A (bool * bool) := 
    {f x := x}.
  Elpi AddAllInstances.

  Goal A (bool * bool). apply _. Qed.
  
End B.