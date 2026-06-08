(* This is the same derivation set exported by derive.std, kept explicit so
   each standard derivation is tested independently. *)
From elpi.apps Require Import
  derive
  derive.map
  derive.lens
  derive.lens_laws
  derive.param1
  derive.param1_congr
  derive.param1_trivial
  derive.param1_functor
  derive.param2
  derive.induction
  derive.tag
  derive.fields
  derive.eqb
  derive.eqbcorrect
  derive.eqbOK.

Module MutualUnsupported.
  Inductive tree : Type :=
  | node (f : forest)
  with forest : Type :=
  | empty
  | cons (t : tree) (f : forest).

  #[only(map)] derive tree.
  #[only(lens)] derive tree.
  #[only(lens_laws)] derive tree.
  #[only(param1)] derive tree.
  #[only(param1_congr)] derive tree.
  #[only(param1_trivial)] derive tree.
  #[only(param1_functor)] derive tree.
  #[only(param2)] derive tree.
  #[only(induction)] derive tree.
  #[only(tag)] derive tree.
  #[only(fields)] derive tree.
  #[only(eqb)] derive tree.
  #[only(eqbcorrect)] derive tree.
  #[only(eqbOK)] derive tree.
End MutualUnsupported.

Module ParametrizedMutualUnsupported.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  #[only(map)] derive ptree.
  #[only(lens)] derive ptree.
  #[only(lens_laws)] derive ptree.
  #[only(param1)] derive ptree.
  #[only(param1_congr)] derive ptree.
  #[only(param1_trivial)] derive ptree.
  #[only(param1_functor)] derive ptree.
  #[only(param2)] derive ptree.
  #[only(induction)] derive ptree.
  #[only(tag)] derive ptree.
  #[only(fields)] derive ptree.
  #[only(eqb)] derive ptree.
  #[only(eqbcorrect)] derive ptree.
  #[only(eqbOK)] derive ptree.
End ParametrizedMutualUnsupported.

(*
Module IndexedMutualUnsupported.
  Inductive even : nat -> Type :=
  | evenO : even 0
  | evenS n : odd n -> even (S n)
  with odd : nat -> Type :=
  | oddS n : even n -> odd (S n).

  #[only(map)] derive even.
  #[only(lens)] derive even.
  #[only(lens_laws)] derive even.
  #[only(param1)] derive even.
  #[only(param1_congr)] derive even.
  #[only(param1_trivial)] derive even.
  #[only(param1_functor)] derive even.
  #[only(param2)] derive even.
  #[only(induction)] derive even.
  #[only(tag)] derive even.
  #[only(fields)] derive even.
  #[only(eqb)] derive even.
  #[only(eqbcorrect)] derive even.
  #[only(eqbOK)] derive even.
End IndexedMutualUnsupported.
*)
