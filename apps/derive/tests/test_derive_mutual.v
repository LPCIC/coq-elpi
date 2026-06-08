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

  Fail #[only(map)] derive tree.
  Fail #[only(lens)] derive tree.
  Fail #[only(lens_laws)] derive tree.
  Fail #[only(param1)] derive tree.
  Fail #[only(param1_congr)] derive tree.
  Fail #[only(param1_trivial)] derive tree.
  Fail #[only(param1_functor)] derive tree.
  Fail #[only(param2)] derive tree.
  Fail #[only(induction)] derive tree.
  Fail #[only(tag)] derive tree.
  Fail #[only(fields)] derive tree.
  Fail #[only(eqb)] derive tree.
  Fail #[only(eqbcorrect)] derive tree.
  Fail #[only(eqbOK)] derive tree.
End MutualUnsupported.

Module ParametrizedMutualUnsupported.
  Inductive ptree (A : Type) : Type :=
  | pnode (x : A) (f : pforest A)
  with pforest (A : Type) : Type :=
  | pempty
  | pcons (t : ptree A) (f : pforest A).

  Fail #[only(map)] derive ptree.
  Fail #[only(lens)] derive ptree.
  Fail #[only(lens_laws)] derive ptree.
  Fail #[only(param1)] derive ptree.
  Fail #[only(param1_congr)] derive ptree.
  Fail #[only(param1_trivial)] derive ptree.
  Fail #[only(param1_functor)] derive ptree.
  Fail #[only(param2)] derive ptree.
  Fail #[only(induction)] derive ptree.
  Fail #[only(tag)] derive ptree.
  Fail #[only(fields)] derive ptree.
  Fail #[only(eqb)] derive ptree.
  Fail #[only(eqbcorrect)] derive ptree.
  Fail #[only(eqbOK)] derive ptree.
End ParametrizedMutualUnsupported.

Module IndexedMutualUnsupported.
  Inductive even : nat -> Type :=
  | evenO : even 0
  | evenS n : odd n -> even (S n)
  with odd : nat -> Type :=
  | oddS n : even n -> odd (S n).

  Fail #[only(map)] derive even.
  Fail #[only(lens)] derive even.
  Fail #[only(lens_laws)] derive even.
  Fail #[only(param1)] derive even.
  Fail #[only(param1_congr)] derive even.
  Fail #[only(param1_trivial)] derive even.
  Fail #[only(param1_functor)] derive even.
  Fail #[only(param2)] derive even.
  Fail #[only(induction)] derive even.
  Fail #[only(tag)] derive even.
  Fail #[only(fields)] derive even.
  Fail #[only(eqb)] derive even.
  Fail #[only(eqbcorrect)] derive even.
  Fail #[only(eqbOK)] derive even.
End IndexedMutualUnsupported.
