From Coq Require Ltac.
Declare ML Module "elpi_plugin".

(* For internal use *)
Lemma hole : Prop. Proof. exact True. Qed.

(* For discriminate *)
Lemma bool_discr : true = false -> forall T : Type, T.
Proof.
exact (fun h T =>
  eq_rect true (fun x => match x with false => T | _ => True end) I false h).
Qed.

Lemma eq_f (T1 : Type) (T2 : Type) (f : T1 -> T2) a b : a = b -> f a = f b.
Proof.
exact (fun h =>
  eq_rect a (fun x => f a = f x) (eq_refl (f a)) b h).
Qed.