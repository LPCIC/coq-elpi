

From elpi Require Import elpi.

Elpi Command declarations.
Elpi Accumulate lp:{{

main [indt-decl A] :- !,
  coq.say "raw:" A,
  std.assert-ok! (coq.typecheck-indt-decl A) "Illtyped inductive declaration",
  coq.say "typed:" A,
  coq.env.add-indt A _.
main [const-decl N (some BO) A] :- !,
  coq.arity->term A TY,
  std.assert-ok! (coq.typecheck BO TY) "illtyped definition",
  coq.env.add-const N BO TY _ _.
main [const-decl N none A] :- !,
  coq.arity->term A TY,
  std.assert-ok! (coq.typecheck-ty TY _) "illtyped axiom",
  coq.env.add-axiom N TY _.
main [ctx-decl (context-item "T" _ _ none t\
                context-item "x" _ t none _\
                context-item "l" _ _ (some _) _\
                context-end)].

main Args :- coq.error Args.
}}.
Elpi Typecheck.

#[arguments(raw)]
Elpi Command raw_declarations.
Elpi Accumulate lp:{{

main [indt-decl RA] :- !,
  coq.say "raw:" RA,
  std.assert-ok! (coq.elaborate-indt-decl-skeleton RA A) "Illtyped inductive declaration",
  coq.say "typed:" A,
  coq.env.add-indt A _.
main [const-decl N (some RBO) RA] :- !,
  coq.arity->term RA RTY,
  std.assert-ok! (coq.elaborate-ty-skeleton RTY _ TY) "illtyped arity", 
  std.assert-ok! (coq.elaborate-skeleton RBO TY BO) "illtyped definition",
  coq.env.add-const N BO TY _ _.
main [const-decl N none RA] :- !,
  coq.arity->term RA RTY,
  std.assert-ok! (coq.elaborate-ty-skeleton RTY _ TY) "illtyped axiom",
  coq.env.add-axiom N TY _.
main [ctx-decl (context-item "T" _ _ none t\
                context-item "x" _ t none _\
                context-item "l" _ _ (some _) _\
                context-end)].

main Args :- coq.error Args.
}}.
Elpi Typecheck.

(*****************************************)
Module anonymous_fields.
Elpi declarations
Record foo := {
  f : nat -> nat;
  _ : f 0 = 0;
}.
Fail Check _elpi_ctx_entry_2_.
End anonymous_fields.

Module raw_anonymous_fields.
Elpi raw_declarations
Record foo := {
  f : nat -> nat;
  _ : f 0 = 0;
}.
Fail Check _elpi_ctx_entry_2_.
End raw_anonymous_fields.

(*****************************************)

Module record_attributes.
Elpi declarations
Record foo A (B : A) : Type := {
    a (_: A) (_ : A) : A;
    z (a : A) :>  B = B -> A;
#[canonical=no]
    x (w := 3) : forall x, a x x = x;
  }.
Elpi Query lp:{{
  coq.locate "foo" (indt I),
  coq.env.projections I [some _, some _, some _].
}}.
End record_attributes.

Module raw_record_attributes.
Elpi raw_declarations
Record foo A (B : A) : Type := {
    a (_: A) (_ : A) : A;
    z (a : A) :>  B = B -> A;
#[canonical=no]
    x (w := 3) : forall x, a x x = x;
  }.
Elpi Query lp:{{
  coq.locate "foo" (indt I),
  coq.env.projections I [some _, some _, some _].
}}.
End raw_record_attributes.

(*****************************************)

Module inductive_nup.
Elpi declarations
  Inductive foo1 {A1} (A2 : A1) | (B1 B2 : Type) : nat -> Type :=
  | a_k1 : forall x, foo1 (B1 * B1)%type B2 3 -> foo1 B1 B2 x
  | a_k2 : A1 -> foo1 B1 B2 1.
Check foo1 _ _ _ _ : Type.
Fail Check (foo1 _ _ _ _ _).
Check a_k1 _ _ _ 3 _ : foo1 _ _ _ 3.
Unset Auto Template Polymorphism.
Inductive r (A : Type) (a : A) := R { f :> A -> A; g : A; p : a = g }.
End inductive_nup.

Module raw_inductive_nup.
Elpi raw_declarations
  Inductive foo1 {A1} (A2 : A1) | (B1 B2 : Type) : nat -> Type :=
  | a_k1 : forall x, foo1 (B1 * B1)%type B2 3 -> foo1 B1 B2 x
  | a_k2 : A1 -> foo1 B1 B2 1.
Check foo1 _ _ _ _ : Type.
Fail Check (foo1 _ _ _ _ _).
Check a_k1 _ _ _ 3 _ : foo1 _ _ _ 3.
Unset Auto Template Polymorphism.
Inductive r (A : Type) (a : A) := R { f :> A -> A; g : A; p : a = g }.
End raw_inductive_nup.

(*****************************************)


Module definition.
Elpi declarations
Definition x1 (P : Type) (w : P) (n : nat) := (n + 1).
Check x1 : forall P, P -> nat -> nat.
Check refl_equal _ : x1 = fun P w n => n + 1.
Elpi declarations  Axiom y (n : nat) : Type.
Check y : nat -> Type.
End definition.

Module raw_definition.
Elpi raw_declarations
Definition x1 (P : Type) (w : P) (n : nat) := (n + 1).
Check x1 : forall P, P -> nat -> nat.
Check refl_equal _ : x1 = fun P w n => n + 1.
Elpi declarations  Axiom y (n : nat) : Type.
Check y : nat -> Type.
End raw_definition.

(*****************************************)

Module section.
Elpi declarations  Context T (x : T) (l := 3).
End section.

Module raw_section.
Elpi raw_declarations  Context T (x : T) (l := 3).
End raw_section.


(*****************************************)

Module full_definition.
Elpi declarations
Definition x (n : nat) := Eval compute in (1 + n).
Goal x 1 = 2.
unfold x.
match goal with |- 2 = 2 => reflexivity end.
Qed.
Definition y (n : nat) : nat := ltac:(exact 1 + n).
End full_definition.

(*****************************************)

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
     (field [coercion tt] "f" (prod `_` c0 _\ c0) c2\
      field [] "g" c0 c3\
      field [] "p" (app [global (indt _), c0, c1, c3]) _\
      end-record)) "not a record",
  coq.env.add-indt R _.
}}.

Print r.
End copy.