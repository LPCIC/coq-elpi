From elpi.apps Require Import tc.

Elpi TC Solver Override TC.Solver All.

(* Base test *)
Section S1.

  TC.Declare Class class1 (n : nat).
  
  (* TODO: here coq can solve the goal without applying Build_class1 *)
  Instance inst1 : class1 3. Proof. apply Build_class1. Qed.

  Goal exists x, class1 x. Proof. eexists. apply _. Qed.

End S1.

(* Deterministic class test *)
Section S2.

  #[deterministic] TC.Declare Class class2 (n : nat).

  Instance inst2  : class2 1 | 0. Proof. apply Build_class2. Qed.
  Instance inst2' : class2 2 | 1. Proof. apply Build_class2. Qed.

  Class aux (i: nat).

  Instance inst_aux  : forall n, class2 n -> aux n -> aux 3. Qed.
  Section S2'.
    Local Instance inst_aux' : aux 1. Qed.
    Goal aux 3. apply _. Qed.
  End S2'.

  Section S2'.
    Local Instance inst_aux'' : aux 2. Qed.
    Goal aux 3. 
    Proof. 
      Succeed apply (inst_aux 2 inst2' inst_aux'').
      (* Note: since class2 is deterministic we cannot backtrack. 
               The first hypothesis of inst_aux is unified to inst2, 
               this causes `aux 2` to fail. The instance inst2' is not tried 
               due to the deterministic class  *)
      Fail apply _.
    Abort.
  End S2'.

End S2.

(* Mode test *)
Section S3.
  #[mode(i)] TC.Declare Class class3 (n : nat).
  Instance inst3 : class3 0. Proof. apply Build_class3. Qed.

  (* Elpi Print TC.Solver "elpi.apps.tc.examples/TC.Solver". *)

  Goal exists x, class3 x. 
  Proof.
    eexists.
    Succeed apply inst3.
    Fail apply _.
  Abort.

End S3.

Section S31.
  #[mode(o=ff)] TC.Declare Class class31 (n : nat).
  Instance inst31 : class31 0. Proof. apply Build_class31. Qed.

  Goal exists x, class31 x. 
  Proof.
    eexists.
    Succeed apply inst31.
    Fail apply _.
  Abort.

End S31.

