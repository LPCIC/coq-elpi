From elpi.apps Require Import tc.

Class EqDec (A : Type) :=
  { eqb : A -> A -> bool ;
    eqb_leibniz : forall x y, eqb x y = true -> x = y }.

Generalizable Variables A.

Class Ord `(E : EqDec A) := { le : A -> A -> bool }.

Class C (A : Set).

Elpi TC Solver Override TC.Solver All.
Global Instance cInst `{e: EqDec nat} : Ord e -> C nat. Admitted.

(* 
  We want to be sure that cInst when compiled has only one hypothesis: (Ord e).
  We don't want the hypothesis {e : EqDec nat} since it will be verified by (Ord e)
*)
(* TODO: it should not fail *)
Fail Elpi Query TC.Solver lp:{{
  compile {{:gref cInst}} _ _ CL,
  CL = (pi a\ pi b\ (_ :- (Hyp a b))),
  coq.say Hyp,
  pi a b\ 
    expected-found (do _) (Hyp a b).
}}.



