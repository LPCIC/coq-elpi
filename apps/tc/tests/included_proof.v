From elpi Require Import compiler.

Class EqDec (A : Type) :=
  { eqb : A -> A -> bool ;
    eqb_leibniz : forall x y, eqb x y = true -> x = y }.

Generalizable Variables A.

Class Ord `(E : EqDec A) := { le : A -> A -> bool }.

Class C (A : Set).

Global Instance cInst `{e: EqDec nat} : Ord e -> C nat. Admitted.

Elpi AddAllClasses.

(* 
  We want to be sure that cInst when compiled has only one hypothesis: (Ord e).
  We don't want the hypothesis {e : EqDec nat} since it will be verified by (Ord e)
*)
Elpi Query TC_solver lp:{{
  compile {{:gref cInst}} _ _ CL.
  CL = (pi a\ pi b\ (_ :- do (Hyp a b))),
  pi a b\ 
    expected-found 1 {std.length (Hyp a b)}.
}}.



