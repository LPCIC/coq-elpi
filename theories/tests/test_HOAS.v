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

Elpi Command declarations.
Elpi Accumulate lp:{{
main [indt-decl A] :-
  coq.typecheck-indt-decl A ok, coq.env.add-indt A _.
main [const-decl N (some BO) (some TY)] :-
  coq.typecheck BO TY ok,
  coq.env.add-const N BO TY _ _ _.
main [const-decl N none (some TY)] :-
  coq.typecheck-ty TY _ ok,
  coq.env.add-const N _ TY _ _ _.
main [ctx-decl C] :-
  coq.typecheck C _ ok,
  coq.say C.

main Args :- coq.error Args.
}}.
Elpi Typecheck.

Elpi declarations  Record foo A : Type := {
    a of A & A : A;
    z (a : A) :>  A -> A;
    x (w := 3) : forall x, a x x = x;
  }.
Print foo.
About z.

Elpi declarations  Definition x1 (n : nat) := (n + 1).

Print x1.

Elpi declarations  Axiom y (n : nat) : Type.

Print y.

Elpi declarations  Context T (x : T) (l := 3).
