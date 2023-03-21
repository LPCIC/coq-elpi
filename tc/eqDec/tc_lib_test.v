From Coq Require Import EquivDec Arith Program.Utils.
Require Import String.
Open Scope string_scope.

Check (fun a b : list nat => a == b).
Check (fun a b : (list bool * list nat) => a == b).
Compute (false == true).
Check (nil == nil).
Check (8 == 9).
Compute (8 == 8).
Compute (8 <> 8).
Check ("aa" == "b").
Check (equiv 2  2).
