(**
   This example shows how to use derive
*)

From elpi.apps Require Import derive.
Set Uniform Inductive Parameters.

(** The basic invocation is with just one argument, the inductive
    type name *)
derive nat.

(** generated constants are prefixed with nat_ *)
Check nat_eq_OK :
  forall x y, reflect (x = y) (nat_eq x y).

(** One can also prefix an Inductive declaration with derive. *)
derive
Inductive tickle A := stop | more : A -> tickle -> tickle.

(** In this case the command is elaborated to:

  Module tickle.
    Inductive tickle A := stop | more : A -> tickle -> tickle.
    derive tickle.
  End tickle.
  Notation tickle := tickle.tickle.
  Notation stop := tickle.stop.
  Notation more := tickle.more.
*)
Check more :
  forall A, A -> tickle A -> tickle A.

(** Some goodies *)
Check tickle.eq : (* eq test *)
  forall A, (A -> A -> bool) -> tickle A -> tickle A -> bool.

Check tickle.eq_OK : (* eq test correctness proof *)
  forall A f, (forall x y, reflect (x = y) (f x y)) -> forall x y, reflect (x = y) (tickle.eq A f x y).

Check tickle.map : (* map the container *)
  forall A B, (A -> B) -> tickle A -> tickle B.

Check tickle.isk_stop : (* recognize a constructor *)
  forall A, tickle A -> bool.

Check tickle.tickle_R : (* relator (binary parametricity translation) *)
  forall A B, (A -> B -> Type) -> tickle A -> tickle B -> Type.

(** This is a tricky case, since you need a good induction principle for the
    nested occurrence of tickle. #[verbose] prints all the derivations being
    run *)
#[verbose] derive
Inductive rtree A := Leaf (a : A) | Node (l : tickle rtree).

Check rtree.induction : (* this is the key *)
  forall A PA P,
  (forall a, PA a -> P (Leaf A a)) ->
  (forall l, tickle.is_tickle (rtree A) P l -> P (Node A l)) ->
  forall x, rtree.is_rtree A PA x -> P x.

Check rtree.eq_OK nat nat_eq nat_eq_OK : (* proofs compose *)
  forall x y : rtree nat, reflect (x = y) (rtree.eq nat nat_eq x y).

(** You can also select which derivations you like *)
#[only(lens_laws, eq)] derive
Record Box A := { contents : A; tag : nat }.

Check Box.eq :
  forall A, (A -> A -> bool) -> Box A -> Box A -> bool.

Check @Box._tag : (* the Lens for the second field (A is implicit) *)
  forall A, Lens (Box A) (Box A) nat nat.

Check Box._tag_set_set : (* a Lens law *)
  forall A (r : Box A) y x, set Box._tag x (set Box._tag y r) = set Box._tag x r.

Check Box._tag_contents_exchange : (* another one *)
  forall A (r : Box A) x y, set Box._tag x (set Box._contents y r) =
                            set Box._contents y (set Box._tag x r).
