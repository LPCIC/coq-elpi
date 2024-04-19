From elpi Require Import tc.

Class A (t : nat -> nat) (t' : Type).
Class B (t : nat) (t' : Type).

(* Elpi Trace Browser. *)
Instance Innnn: forall b (c : nat -> nat),
  (forall a, B (c a) b) -> A c b.
Qed.

Instance Immmm : B 3 bool.
Qed.
Elpi Print TC.Solver.

Goal exists x, A x bool.
eexists.
  apply (Innnn bool (fun _ => 3) (fun x => Immmm)).
Elpi Override TC TC.Solver None.
Set Elpi Typeclasses Debug.
Timeout 3 apply _.
Show Proof.
Qed.
