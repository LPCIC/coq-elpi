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
main [ctx-decl (context-item "T" _ none (t\ context-item "x" t none (_\ context-item "l" _ (some _) _\ context-end)))].

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


Elpi Command kwd.
Elpi Accumulate lp:{{
  main L :- coq.say L.
}}.
Elpi Typecheck.

Elpi kwd fun in as 4 end match return => : := { } ; , | "x" 1 H (match x as y in False return nat with end).

Elpi Query lp:{{
  coq.env.begin-section "xxxxx",
  coq.univ.new [] U,
  T = sort (typ U),
  coq.env.add-const "a" _ T tt tt _,
  coq.env.end-section
}}.

Elpi Db univs.db lp:{{ pred u o:univ. }}.
Elpi Command test_u.
Elpi Accumulate Db univs.db.
Fail Elpi Query lp:{{
  coq.univ.new [] U,
  coq.elpi.accumulate current "univs.db" (clause _ _ (u U))
}}.

Universe foo.

Elpi Query lp:{{
  {{ Type@{foo} }} = sort (typ U),
  coq.elpi.accumulate current "univs.db" (clause _ _ (u U))
}}.
