From elpi Require Import elpi.

Elpi Tactic test1.
Elpi Accumulate lp:{{

solve _ [G] GS :- pi x\
  coq.sigma.print,
  print_constraints,
  refine {{ fun w : _ => _ }} G GS.
}}.
Elpi Typecheck.

Lemma test (x : nat) : bool -> True.
Proof.

elpi test1.

Abort.

Ltac foobar x := eapply x.

(* TODO: test evar type with a binder *)

Elpi Tactic test2.
Elpi Accumulate lp:{{

solve _ [G] GS :-
  G = goal [decl T A B | _ ] _ _ _,
  decl T A B => 
  coq.ltac1.call "foobar" [T] G GS,
  coq.say GS.

}}.




Lemma test  : (forall b: ( forall b : bool, b = b), True) -> True.
Proof.
intro.
elpi test2.
intro; reflexivity.
Qed.


From Coq Require Import ssreflect.

Elpi Command tele.
Elpi Accumulate lp:{{
main [indt-decl A] :-
  coq.say A,
  coq.typecheck-indt-decl A ok,
  coq.env.add-indt A _.
}}.
Elpi Typecheck.
Elpi tele  Record foo A : Type := {
    a of A & A : A;
    z (a : A) :>  A -> A;
    x (w := 3) : forall x, a x x = x;
  }.
Print foo.
About z.