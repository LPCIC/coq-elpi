(* README *)
From elpi.apps Require Import derive.std.

#[module] derive Inductive peano := Zero | Succ (p : peano).

Print peano.peano.
(* Inductive peano : Set :=  Zero : peano | Succ : peano -> peano. *)

Eval compute in peano.eqb Zero (Succ Zero).
(* = false : bool *)

About peano.eqb_OK.
(*
peano.eqb_OK : forall x1 x2 : peano, reflect (x1 = x2) (peano.eqb x1 x2)

peano.eqb_OK is not universe polymorphic
Arguments peano.eqb_OK x1 x2
peano.eqb_OK is opaque
Expands to: Constant elpi.apps.derive.examples.readme.peano.eqb_OK
*)

#[verbose] derive Nat.add.
Check is_add. (*
: forall n : nat, is_nat n ->
  forall m : nat, is_nat m ->
    is_nat (n + m)
*)
