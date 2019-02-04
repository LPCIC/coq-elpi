From elpi Require Import test_derive_stdlib derive.projK.

Module Coverage.
Elpi derive.projK Coverage.empty.
Elpi derive.projK Coverage.unit.
Elpi derive.projK Coverage.peano.
Elpi derive.projK Coverage.option.
Elpi derive.projK Coverage.pair.
Elpi derive.projK Coverage.seq.
Elpi derive.projK Coverage.rose.
Elpi derive.projK Coverage.nest.
Elpi derive.projK Coverage.w.
Elpi derive.projK Coverage.vect.
Elpi derive.projK Coverage.dyn.
Elpi derive.projK Coverage.zeta.
Elpi derive.projK Coverage.beta.
Elpi derive.projK Coverage.iota.
Elpi derive.projK Coverage.large.
End Coverage.
Set Implicit Arguments.

Elpi derive.projK nat.

Lemma test_proj1S x : projS1 33 (S x) = x.
Proof. split. Qed.

Require Vector.

Elpi derive.projK Vector.t. Check projcons3.

Arguments Vector.nil {_}.
Inductive Box A : nat -> Type :=
 | mkB (T : Type) (a : A) i (t : Vector.t T i) : Box A (S i)
 | Oops : Box A 0.

Elpi derive.projK Box.

Lemma test_projmkB1 A (a : A) d1 d2 d3 d4 :
  @projmkB1 A 1 d1 d2 d3 d4 (@mkB A bool a 0 Vector.nil) = bool.
Proof. split. Qed.

Lemma test_projmkB2 A (a : A) d1 d2 d3 d4 :
  @projmkB2 A _ d1 d2 d3 d4 (@mkB A bool a 0 Vector.nil) = a.
Proof. split. Qed.

Lemma test_projmkB3 A (a : A) d1 d2 d3 d4 :
  @projmkB3 A _ d1 d2 d3 d4 (@mkB A bool a 0 Vector.nil) = 0.
Proof. split. Qed.

Lemma test_projmkB4 A (a : A) d1 d2 d3 d4 :
  @projmkB4 A _ d1 d2 d3 d4 (@mkB A bool a 0 Vector.nil) =
      existT (fun T => { i : nat & Vector.t T i}) bool
        (existT (fun i => Vector.t bool i) 0 Vector.nil).
Proof. split. Qed.

Inductive rtree A : Type :=
  Leaf (n : A) | Node (l : list (rtree A)).
Elpi derive.projK rtree.
