From elpi.apps Require Import tc.
From Coq Require Import EquivDec.

TC.AddAllClasses.
TC.AddAllInstances.

#[deterministic] TC.Declare Class NoBacktrack (n: nat).
TC.Declare Class A (n: nat).
TC.Declare Class B.

Instance nb0 : NoBacktrack 0. Proof. split. Qed.
Instance nb1 : NoBacktrack 1. Proof. split. Qed.

Instance a0 : A 0. Proof. split. Qed.
Instance a3 n : NoBacktrack n -> A n -> B. Proof. split. Qed.

TC.AddAllInstances.

Goal B. Fail apply _. Abort.
