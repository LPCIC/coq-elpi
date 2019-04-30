From Coq Require Ltac Bool.
Declare ML Module "elpi_plugin".

(* We load once and forall these files in this .vo, to ease redistribution *)
Elpi HOAS "coq-HOAS.elpi".
Elpi Checker "etc/coq-elpi-checker.elpi".
Elpi Printer "elpi2html.elpi".
Elpi CommandTemplate "elpi-command.elpi".
Elpi TacticTemplate "elpi-tactic.elpi".

(* For internal use *)
Lemma hole : Prop. Proof. exact True. Qed.

Register hole as elpi.hole.

(* TO BE MOVED AWAY: For discriminate *)
Lemma bool_discr : true = false -> forall T : Type, T.
Proof.
exact (fun h T =>
  eq_rect true (fun x => match x with false => T | _ => True end) I false h).
Qed.

Notation reflect := Bool.reflect.
Notation ReflectF := Bool.ReflectF.
Notation ReflectT := Bool.ReflectT.

Definition eq_axiom T eqb x :=
  forall (y : T), reflect (x = y) (eqb x y).

Definition eq_axiom_at T eqb (x y : T) :=
  reflect (x = y) (eqb x y).

Notation andb := Coq.Init.Datatypes.andb.
Notation true := Coq.Init.Datatypes.true.
Notation false := Coq.Init.Datatypes.false.

Lemma eq_f (T1 : Type) (T2 : Type) (f : T1 -> T2) a b : a = b -> f a = f b.
Proof.
exact (fun h =>
  eq_rect a (fun x => f a = f x) (eq_refl (f a)) b h).
Defined.

Definition contractible T := { x : T & forall y, @eq T x y }.

Definition contracts T P (x : T) w u := (@existT (P x) (fun u : P x => forall v : P x,@eq (P x) u v) w u).

Definition full T P := forall x : T, P x.

Definition trivial T P := forall x : T, contractible (P x).

Definition trivial_full T P (e : trivial T P) (x : T) : P x := projT1 (e x).

Definition trivial_uniq T P (e : trivial T P) (x : T) (p : P x) :
  trivial_full T P e x = p := projT2 (e x) p.