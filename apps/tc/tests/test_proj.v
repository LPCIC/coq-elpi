From elpi Require Import tc.

Record r := mkr {car : Type; rf : car -> car}.

Canonical Structure c := mkr nat (fun x => x).

Class C (T : Type) := {f : T -> T}.

Instance inst c: C (car c). now constructor. Qed.

Goal C nat. apply _. Qed.

