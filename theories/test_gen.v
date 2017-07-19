From elpi Require Import elpi.
Elpi Init "./" "./elpi/".

Elpi Accumulate File "pervasives.elpi".

Inductive LVar A :=
| VLow : A -> LVar A
| VHigh : A -> LVar A.

Inductive LamC (A : Type) :=
| App : LamC A -> LamC A -> LamC A
| Abs : LamC (LVar A) -> LamC A
| Var : A -> LamC A.

(*
  D = * => *; * => *; e
  LVar : Ty D (* => *) * = V0 + D0 . V0
  LamC : Ty D (* => *) * = ((D1 . V0) * (D1 . V0) + D1 . (D0 . V0)) + V0
  VLow A x  = con 0 (inl x)
  VHigh A y = con 0 (inr y)
  App A x y = con 1 (inl (inl (pair x y))
  Abs A x   = con 1 (inl (inr x))
  Var A x   = con 1 (inr x)

## Equality generation

Type :
  Phi S T = S -> Bool

Descriptors :
  doUnit = \x -> true
  doPair phi1 phi2 = \(pair x y) -> phi1 x && phi2 y
  doInl phi = \x -> match x with | Inl y => phi y | Inr y => false end
  doInr phi = \x -> match x with | Inl y => false | Inr y => phi r end
  doCon v phi = \(con _ x) -> phi x

## Equality proof

Type :
  Phi S T = forall (a b : S), eq_ok S eq a b

Descriptors :
  doUnit = conj (fun H => eq_refl) (fun H => eq_refl)
  doPair ph1 ph2 = forall ((pair a1 b1) ((pair a2 b2) : S),
                    conj (proj1 (phi1 a1 b1) ...) (...)
*)

Elpi Accumulate File "gen.elpi".
Elpi Accumulate File "geneq.elpi".
Elpi Run "cleanup-term-test'.".

Inductive SType :=
| stype : Type -> SType.

Definition from_stype (S : SType) : Type :=
match S with
| stype T => T
end.

Inductive PairType (A B : SType) :=
| pair : (from_stype A) -> (from_stype B) -> PairType A B.