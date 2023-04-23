From Coq Require Import EquivDec Arith Program.Utils.
Local Hint Mode EqDec ! - -: typeclass_instances.

(* Set Typeclasses Depth 10. *)
Check (fun x y : nat => x == y).

(* This cause an infinite loop... *)
(* Check (fun x y : _ => x == y). *)

From elpi.apps Require Import tc.compiler.

Elpi Override TC TC_check All.
Elpi AddAllInstances.
Check (fun x y : nat => x == y).
Fail Check (fun x y : _ => x == y).

