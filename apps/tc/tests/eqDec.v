From Coq Require Export EquivDec Arith.
From elpi.apps Require Export tc.compiler.

Elpi Override TC TC_check All.
Elpi add_instances EqDec.

Elpi Accumulate TC_check lp:{{
  :before "hintHook"
  tc _ _ A _ :- coq.say A.
}}.


Set Typeclasses Debug.

Check (fun a b : _ => a == b).