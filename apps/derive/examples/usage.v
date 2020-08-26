(**
   This example shows how to use derive
*)

From elpi.apps Require Import derive.

(** The basic invocation is with just one argument, the inductive
    type name *)
derive nat.
Check nat_eq_OK. (* generated constants are prefixed with nat_ *)

(** One can also prefix an Inductive declaration with derive. *)
derive Inductive tickle {A} := stop | more : A -> tickle -> tickle.

(** In this case the command is elaborated to:

  Module tickle.
    Inductive tickle A := stop | more : A -> tickle-> tickle.
    derive tickle.
  End tickle.
  Notation tickle := tickle.tickle.
  Notation stop := tickle.stop.
  Notation more := tickle.more.
*)
Check more. (* more : forall A, A -> tickle A -> tickle A. *)
Check tickle.eq.
Check tickle.eq_OK.
Check tickle.map.
Check tickle.isk_stop.
Check tickle.tickle_R.

(** This is a tricky case *)
#[verbose] derive Inductive rtree A := Leaf (a : A) | Node (l : @tickle rtree).
Check rtree.eq_OK _ _ nat_eq_OK.
