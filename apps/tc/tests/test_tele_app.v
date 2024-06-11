From elpi.apps Require Import tc.
(* From stdpp/telescopes.v *)

(* A test where polymorphic universes are used *)

Polymorphic Inductive tele : Type :=
  | TeleO : tele
  | TeleS {X} (binder : X -> tele) : tele.

Polymorphic Fixpoint tele_fun (TT : tele) (T : Type) : Type :=
  match TT with
  | TeleO => T
  | TeleS b => forall x, tele_fun (b x) T
  end.

Class FMap (X : Type -> Type).

(* 
  Since the instance is polymorphic, then the proof of the compiled elpi rule
  should be wrapped inside the pglobal constructor
*)
Polymorphic Instance tele_fmap {TT : tele} : FMap (tele_fun TT) := {}.

Goal forall x, FMap (tele_fun x).
  intros.
  apply _.
  Show Proof.
Qed.