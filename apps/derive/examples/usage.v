(**
   This example shows how to use derive
*)

From Coq Require Import Bool.
From elpi.apps Require Import derive.std.
Set Uniform Inductive Parameters.

(** The best way to call derive is to prefix an Inductive declaration. *)
derive
Inductive tickle A := stop | more : A -> tickle -> tickle.

(** The command is elaborated to something like:

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
Check tickle.eqb : (* eq test *)
  forall A, (A -> A -> bool) -> tickle A -> tickle A -> bool.

Check tickle.eqb_OK : (* eq test correctness proof *)
  forall A f, (forall x y, reflect (x = y) (f x y)) -> forall x y, reflect (x = y) (tickle.eqb A f x y).

Check tickle.map : (* map the container *)
  forall A B, (A -> B) -> tickle A -> tickle B.

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

(** You can also select which derivations you like *)
#[verbose, only(lens_laws, eqb)] derive
Record Box A := { contents : A; tag : nat }.

Check Box.eqb :
  forall A, (A -> A -> bool) -> Box A -> Box A -> bool.

Import lens.

Check @Box._tag : (* the Lens for the second field (A is implicit) *)
  forall A, Lens (Box A) (Box A) nat nat.

Check Box._tag_set_set : (* a Lens law *)
  forall A (r : Box A) y x, set Box._tag x (set Box._tag y r) = set Box._tag x r.

Check Box._tag_contents_exchange : (* another one *)
  forall A (r : Box A) x y, set Box._tag x (set Box._contents y r) =
                            set Box._contents y (set Box._tag x r).

(** Finally, one can derive an existing inductive type.
    Generated constants are
    prefixed with nat_ but won't be in the right
    place, which is where the type is defined. This means that two users
    may run derive for the same type in different files, leading to
    duplication. *)

derive nat.

Check nat_eqb_OK :
  forall x y, reflect (x = y) (nat_eqb x y).

(** Once can also run derive recursively, but this has the same bad effect,
    all generated concepts will be out of place *)

Inductive a := A.
Inductive b := B : a -> b.

#[recursive, only(eqbOK)] derive b.

Check a_eqb.
Check b_eqb.
