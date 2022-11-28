(* README *)                            
From elpi.apps Require Import derive.std.
 
derive Inductive peano := Zero | Succ (p : peano).

(* Bug 8.16: About peano.peano.*)
(* Notation peano := peano.peano *)

Print peano.peano.
(* Inductive peano : Type :=  Zero : peano | Succ : peano -> peano *)

Eval compute in peano.eqb Zero (Succ Zero).
(* = false : bool *)

About peano.eqb_OK.
(*
peano.eqb_OK : forall x1 x2 : peano, Bool.reflect (x1 = x2) (peano.eqb x1 x2)

peano.eqb_OK is not universe polymorphic
Arguments peano.eqb_OK x1 x2
peano.eqb_OK is opaque
*)

#[verbose] derive Nat.add.
Check is_add. (*
: forall n : nat, is_nat n ->
  forall m : nat, is_nat m ->
    is_nat (n + m)
*)