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


Elpi Command declarations.
Elpi Accumulate lp:{{

main [indt-decl A] :- !,
  coq.say "raw:" A,
  std.assert-ok! (coq.typecheck-indt-decl A) "Illtyped inductive declaration",
  coq.say "typed:" A,
  coq.env.add-indt A _.
main [const-decl N (some BO) A] :- !,
  coq.arity->term A TY,
  coq.typecheck BO TY ok,
  coq.env.add-const N BO TY _ _.
main [const-decl N none A] :- !,
  coq.arity->term A TY,
  coq.typecheck-ty TY _ ok,
  coq.env.add-axiom N TY _.
main [ctx-decl (context-item "T" _ _ none t\
                context-item "x" _ t none _\
                context-item "l" _ _ (some _) _\
                context-end)].

main Args :- coq.error Args.
}}.
Elpi Typecheck.

Module anonymous_fields.

Elpi declarations Record foo := {
  f : nat -> nat;
  _ : f 0 = 0;
}.
Fail Check _elpi_ctx_entry_2_.

End anonymous_fields.

From Coq Require Import ssreflect.

Module record_attributes.

Elpi declarations
Record foo A (B : A) : Type := {
    a of A & A : A;
    z (a : A) :>  B = B -> A;
#[canonical=no]
    x (w := 3) : forall x, a x x = x;
  }.

Elpi Query lp:{{
  coq.locate "foo" (indt I),
  coq.CS.canonical-projections I [some _, some _, some _].
}}.

End record_attributes.

Module inductive_nup.

Elpi declarations
  Inductive foo1 {A1} (A2 : A1) | B1 (B2 : Type) : nat -> Type :=
  | a_k1 : forall x, foo1 A2 (B1 * B1)%type B2 3 -> foo1 A2 B1 B2 x
  | a_k2 : A1 -> foo1 A2 B1 B2 1.
Print foo1.
Check foo1 _ _ _ _ : Type.
Fail Check (foo1 _ _ _ _ _).
Check a_k1 _ _ _ 3 _ : foo1 _ _ _ 3.

Inductive r (A : Type) (a : A) := R { f :> A -> A; g : A; p : a = g }.

End inductive_nup.

Module definition.

Elpi declarations  Definition x1 (P : Type) (w : P) (n : nat) := (n + 1).

Check x1 : forall P, P -> nat -> nat.
Check refl_equal _ : x1 = fun P w n => n + 1.

Elpi declarations  Axiom y (n : nat) : Type.

Check y : nat -> Type.

End definition.

Module section.

Elpi declarations  Context T (x : T) (l := 3).

End section.

Module copy.
Import inductive_nup.

Elpi Query lp:{{
  coq.locate "foo1" (indt I),
  coq.env.indt-decl I D,
  coq.say D,
  coq.env.add-indt D _.
}}.
Check foo1 _ _ _ _ : Type.
Fail Check (foo1 _ _ _ _ _).
Check a_k1 _ _ _ 3 _ : foo1 _ _ _ 3.


Elpi Query lp:{{
  coq.locate "r" (indt I),
  coq.env.indt-decl I R,
  std.assert! (R = 
    parameter "A" explicit (sort (typ _)) c0 \
    parameter "a" explicit c0 c1 \
    record "r" (sort (typ _)) "R"
     (field [] "f" (prod `_` c0 _\ c0) c2\
      field [] "g" c0 c3\
      field [] "p" (app [global (indt _), c0, c1, c3]) _\
      end-record)) "not a record",
  coq.env.add-indt R _.
}}.

Print r.
End copy.

Module kwd.

Parameter x : bool.

Elpi Command kwd.
Elpi Accumulate lp:{{
  main L :- coq.say L.
}}.
Elpi Typecheck.

Elpi kwd fun in as 4 end match return => : := { } ; , | "x" 1 H (match x as y in False return nat with end).

End kwd.

Elpi Query lp:{{
  coq.env.begin-section "xxxxx",
  coq.univ.new [] U,
  T = sort (typ U),
  coq.env.add-section-variable "a" T _,
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


Axiom B : bool -> Type.
Axiom N : nat -> Type.

(* restriction *)
Elpi Query lp:{{
  pi w\
  @pi-decl `a` {{ bool }} a\
  pi e\
  @pi-decl `b` {{ B lp:a }} b\
  coq.typecheck {{ fun x (y z : N x) => lp:{{ X a {{x}} {{z}} }} }} _ ok.
}}.


(* option *)
Fail Elpi Query lp:{{
  @pi-decl `a` {{ bool }} a\
    coq.typecheck (X a a) _ ok
}}.
Elpi Query lp:{{
  @pi-decl `a` {{ bool }} a\
  coq.say "----------------------------------",
  @holes! => coq.typecheck (X a a) TY ok,
  coq.sigma.print,
  coq.say (X a a) ":" TY.
}}.

(* primitive *)
Elpi Command primitive.
Elpi Accumulate lp:{{
main [trm T] :-
  std.assert! (coq.reduction.vm.whd_all T _ T1) "normal form is not an opinion",
  std.assert! (coq.reduction.cbv.whd_all T T1) "normal form is not an opinion",
  std.assert! (coq.reduction.lazy.whd_all T T1) "normal form is not an opinion",
  coq.say "Raw term:" T "\nNice term:" {coq.term->string T} "\nRed:" {coq.term->string T1}.
}}.
From Coq Require Import PrimInt63.
Open Scope int63_scope.
Elpi primitive (PrimInt63.add 2000000003333002 1).

From Coq Require Import PrimFloat.
Open Scope float_scope.
Elpi primitive (2.4e13 + 1).
