From elpi Require Import tc.

Module M1.
  Axiom T : Type.
  Axiom P : T -> T -> T.

  Class eta (P: T -> T -> T).

  Instance I1: eta P. Qed.

  Goal eta (fun x => P x). Proof. apply _. Qed.
  Goal eta (fun x y => P x y). Proof. apply _. Qed.
End M1.

Module M2.
  Axiom T : Type.
  Axiom P1 : T -> T.
  Axiom P2 : T -> T -> T.

  Class eta (P1 : T -> T) (P2: T -> T -> T).

  Instance I1: eta P1 P2. Qed.

  Goal eta (fun x => P1 x) P2. Proof. apply _. Qed.
  Goal eta P1 (fun x y => P2 x y). Proof. apply _. Qed.
  Goal eta (fun x => P1 x) (fun x y => P2 x y). Proof. apply _. Qed.
End M2.

Module M3.
  Axiom T : Type.
  Axiom P : T -> T.

  Class eta (P: T -> T).
  Class aux (P: T -> T).

  Instance auxInst : aux (fun x => x). Qed.

  Instance I1: forall (P : T -> T), aux (fun x => P x) -> eta P. Qed.

  Goal exists P, eta (fun x => P x). Proof. eexists. apply _. Qed.
End M3.

