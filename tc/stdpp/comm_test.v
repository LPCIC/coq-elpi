From stdpp Require Import base.

Generalizable All Variables.
Axiom P : nat -> nat -> nat -> Prop.
Lemma xx_and (a: nat) b c:
  (a = b /\ b = c  <-> b = c /\ a = b) -> P a b c.
Proof. trivial.  Admitted.

Lemma yy_and a b c :
  Comm iff and -> P a  b c.
Proof. trivial. Admitted.

Goal P 1 2 3.
  (* apply (@yy_and _ _ _ ( _ : Comm iff and)). *)
  apply yy_and.
  typeclasses eauto.
Qed.

Print Instances Comm.
Check ( _ :  Comm iff and ).

Lemma xx_or (a: nat) b c: a = b \/ b = c  <-> b = c \/ a = b.
Proof. apply or_comm. Qed.

Lemma xx_eq (a: nat) b: a = b <-> b = a.
Proof. apply eq_comm. Qed.

Definition tf := true = false.
Definition ft := false = true.

Lemma xx: tf \/ ft  <-> ft \/ tf.
Proof. apply or_comm. Qed.

Compute (eq_comm tf ft).


  
