From elpi Require Import derive.induction derive.param1 derive.map.


From elpi Require Import test_derive_stdlib
  test_param1 test_map.

Module Coverage.
Elpi derive.induction Coverage.empty.
Elpi derive.induction Coverage.unit.
Elpi derive.induction Coverage.peano.
Elpi derive.induction Coverage.option.
Elpi derive.induction Coverage.pair.
Elpi derive.induction Coverage.seq.
Elpi derive.induction Coverage.tree.
Fail Elpi derive.induction Coverage.nest.
Fail Elpi derive.induction Coverage.w.
Elpi derive.induction Coverage.vect.
Fail Elpi derive.induction Coverage.dyn.
Fail Elpi derive.induction Coverage.zeta.
Elpi derive.induction Coverage.beta.
Elpi derive.induction Coverage.iota.
Elpi derive.induction Coverage.large.
End Coverage.

Check Coverage.peano_induction : forall P,
   P Coverage.Zero ->
   (forall n, P n -> P (Coverage.Succ n)) ->
   forall x, Coverage.is_peano x -> P x.

Check Coverage.seq_induction :
  forall (A : Type) (PA : A -> Type) P,
    P (Coverage.Nil A) ->
    (forall x : A, PA x -> forall xs, P xs -> P (Coverage.Cons A x xs)) ->
    forall l, Coverage.is_seq A PA l -> P l.

Check Coverage.vect_induction :
  forall A (PA : A -> Type) (P : forall n, Coverage.is_peano n -> Coverage.vect A n -> Type),
    P Coverage.Zero Coverage.is_Zero (Coverage.VNil A) ->
    (forall a : A, PA a -> forall n, forall nR: Coverage.is_peano n,
     forall v : Coverage.vect A n, P n nR v -> P (Coverage.Succ n) (Coverage.is_Succ n nR) (Coverage.VCons A a n v)) ->
  forall l lR x, Coverage.is_vect A PA l lR x -> P l lR x.



