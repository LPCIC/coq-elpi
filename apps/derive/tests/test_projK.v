From elpi.apps Require Import derive.projK.
From elpi.apps.derive.tests Require Import test_derive_corelib.

Import test_derive_corelib.Coverage.

Module Coverage.
Elpi derive.projK empty.
Elpi derive.projK unit.
Elpi derive.projK peano.
Elpi derive.projK option.
Elpi derive.projK pair.
Elpi derive.projK seq.
Elpi derive.projK box_peano.
Elpi derive.projK rose.
Elpi derive.projK rose_p.
Elpi derive.projK rose_o.
Elpi derive.projK nest.
Elpi derive.projK w.
Elpi derive.projK vect.
Elpi derive.projK dyn.
Elpi derive.projK zeta.
Elpi derive.projK beta.
Elpi derive.projK iota.
Elpi derive.projK large.
Elpi derive.projK prim_int.
Elpi derive.projK prim_float.
Elpi derive.projK prim_string.
Elpi derive.projK fo_record.
Elpi derive.projK pa_record.
Elpi derive.projK pr_record.
Elpi derive.projK dep_record.
Elpi derive.projK enum.
Elpi derive.projK eq.
Elpi derive.projK bool.
Elpi derive.projK sigma_bool.
Elpi derive.projK ord.
Elpi derive.projK val.
Elpi derive.projK mempty.
Elpi derive.projK munit.
Elpi derive.projK mpeano.
Elpi derive.projK moption.
Elpi derive.projK mtree.
End Coverage.

Import Coverage.

Redirect "tmp" Check projSucc1 : peano -> peano -> peano.
Redirect "tmp" Check projSome1 : forall A, A -> option A -> A.
Redirect "tmp" Check projComma1 : forall A B, A -> B -> pair A B -> A.
Redirect "tmp" Check projComma2 : forall A B, A -> B -> pair A B -> B.
Redirect "tmp" Check projCons1 : forall A, A -> seq A -> seq A -> A.
Redirect "tmp" Check projCons2 : forall A, A -> seq A -> seq A -> seq A.
Redirect "tmp" Check projLeaf1 : forall A, A -> rose A -> A.
Redirect "tmp" Check projNode1 : forall A, seq (rose A) -> rose A -> seq (rose A).
Redirect "tmp" Check projConsN1 : forall A, A -> nest (pair A A) -> nest A -> A.
Redirect "tmp" Check projConsN2 : forall A, A -> nest (pair A A) -> nest A -> nest (pair A A).
Redirect "tmp" Check projvia1 : forall A, (A -> w A) -> w A -> (A -> w A).
Redirect "tmp" Check projVCons1 : forall A i, A -> forall j, vect A j -> vect A i -> A.
Redirect "tmp" Check projVCons2 : forall A i, A -> forall j, vect A j -> vect A i -> peano.
Redirect "tmp" Check projVCons3 : forall A i, A -> forall j, vect A j -> vect A i -> { w & vect A w }.
Redirect "tmp" Check projbox1 : forall T, T -> dyn -> Type.
Redirect "tmp" Check projbox2 : forall T, T -> dyn -> { T : Type & T }.
Redirect "tmp" Check projEnvelope1 : forall A, A -> A -> zeta A -> A.
Redirect "tmp" Check eq_refl 0 : projEnvelope1 nat 1 1 (Envelope nat 0 1) = 0.
Redirect "tmp" Check projEnvelope2 : forall A, A -> A -> zeta A -> A.
Redirect "tmp" Check eq_refl 0 : projEnvelope2 nat 1 1 (Envelope nat 1 0) = 0.
Redirect "tmp" Check projRedex1 : forall A, A -> beta A -> A.
Redirect "tmp" Check projWhy1 : forall n : peano, match n return Type with 
                    | Zero => peano
                    | Succ _ => unit
                    end -> iota -> peano.
Redirect "tmp" Check projWhy2 : forall n : peano, match n return Type with 
                    | Zero => peano
                    | Succ _ => unit
                    end -> iota -> { i : peano & match i with Zero => peano | Succ _ => unit end }.
Redirect "tmp" Check projPI1.
Redirect "tmp" Check projPF1.

Redirect "tmp" Check projBuild_fo_record1 : peano -> unit -> fo_record -> peano.
Redirect "tmp" Check projBuild_fo_record2 : peano -> unit -> fo_record -> unit.
Redirect "tmp" Check projBuild_pa_record2 : forall A, peano -> A -> pa_record A -> A.
Redirect "tmp" Check projBuild_pr_record2 : forall A, peano -> A -> pr_record A -> A.

Fail Redirect "tmp" Check projmpeano'1.
Fail Redirect "tmp" Check projmoption'1.
Fail Redirect "tmp" Check projmtree'1.


Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Module UnivPoly.

Inductive Wrap := K : bool -> Wrap.
Elpi derive.projK Wrap.
Redirect "tmp" Compute (eq_refl (projK1 false (K true))) : true = true.

Inductive List (A : Type) := Nil | Cons : A -> List A -> List A.
Elpi derive.projK List.

Inductive Prod (A B : Type) := c : A -> B -> Prod A B.
Elpi derive.projK Prod.
End UnivPoly.

Unset Universe Polymorphism.

From elpi.apps Require Import derive.

Module ProjKStandaloneFirst.
  From elpi.apps Require Import derive.projK.

  Inductive tree : Type := node (f : forest)
  with forest : Type := empty | cons (t : tree) (f : forest).

  Elpi derive.projK tree.

  Redirect "tmp" Check projnode1.
  Redirect "tmp" Check forest_getk_cons1.
  Redirect "tmp" Check forest_getk_cons2.
  Redirect "tmp" Elpi Query derive.projK lp:{{
    coq.locate "node" (indc N),
    coq.locate "cons" (indc C),
    projK-db N 1 _,
    projK-db C 1 _
  }}.
End ProjKStandaloneFirst.

Module ProjKStandaloneSecond.
  From elpi.apps Require Import derive.projK.

  Inductive tree : Type := node (f : forest)
  with forest : Type := empty | cons (t : tree) (f : forest).

  Elpi derive.projK forest.

  Redirect "tmp" Check tree_getk_node1.
  Redirect "tmp" Check projcons1.
  Redirect "tmp" Check projcons2.
End ProjKStandaloneSecond.

Module ProjKMetaFirst.
  From elpi.apps Require Import derive.projK.

  Inductive tree : Type := node (f : forest)
  with forest : Type := empty | cons (t : tree) (f : forest).

  #[only(projK)] derive tree.

  Redirect "tmp" Check tree_getk_node1.
  Redirect "tmp" Check forest_getk_cons1.
  Redirect "tmp" Check forest_getk_cons2.
End ProjKMetaFirst.

Module ProjKMetaSecond.
  From elpi.apps Require Import derive.projK.

  Inductive tree : Type := node (f : forest)
  with forest : Type := empty | cons (t : tree) (f : forest).

  #[only(projK)] derive forest.

  Redirect "tmp" Check tree_getk_node1.
  Redirect "tmp" Check forest_getk_cons1.
  Redirect "tmp" Check forest_getk_cons2.
End ProjKMetaSecond.

Module ProjKPrefixSecond.
  From elpi.apps Require Import derive.projK.

  Inductive tree : Type := node (f : forest)
  with forest : Type := empty | cons (t : tree) (f : forest).

  #[only(projK), prefix="custom_"] derive forest.

  Redirect "tmp" Check tree_getk_node1.
  Redirect "tmp" Check custom_getk_cons1.
  Redirect "tmp" Check custom_getk_cons2.
End ProjKPrefixSecond.

Module ProjKComputation.
  From elpi.apps Require Import derive.projK.

  Inductive tree : Type := node (f : forest)
  with forest : Type := empty | cons (t : tree) (f : forest).

  #[only(projK)] derive tree.

  Example tree_getk_node1_computes :
    tree_getk_node1 empty (node (cons (node empty) empty)) = cons (node empty) empty := eq_refl.
  Example forest_getk_cons1_computes :
    forest_getk_cons1 (node empty) empty (cons (node empty) empty) = node empty := eq_refl.
  Example forest_getk_cons2_computes :
    forest_getk_cons2 (node empty) empty (cons (node empty) (cons (node empty) empty)) =
    cons (node empty) empty := eq_refl.
End ProjKComputation.
