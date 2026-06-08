From elpi Require Import elpi.

Inductive tree : Type :=
| node (f : forest)
with forest : Type :=
| empty
| cons (t : tree) (f : forest).

Inductive ptree (A : Type) : Type :=
| pnode (x : A) (f : pforest A)
with pforest (A : Type) : Type :=
| pempty
| pcons (t : ptree A) (f : pforest A).

Inductive even : nat -> Type :=
| evenO : even 0
| evenS n : odd n -> even (S n)
with odd : nat -> Type :=
| oddS n : even n -> odd (S n).

Elpi Command test_mutind.
Elpi Accumulate lp:{{
main _ :-
  coq.locate "tree" (indt Tree),
  coq.env.indt-decl Tree TreeDecl,
  std.assert-ok! (coq.typecheck-indt-decl TreeDecl) "tree declaration illtyped",

  coq.locate "ptree" (indt PTree),
  coq.env.indt-decl PTree PTreeDecl,
  std.assert-ok! (coq.typecheck-indt-decl PTreeDecl) "ptree declaration illtyped",

  coq.locate "even" (indt Even),
  coq.env.indt-decl Even EvenDecl,
  std.assert-ok! (coq.typecheck-indt-decl EvenDecl) "even declaration illtyped",

  Tree2Decl = (minductive "tree2" tt (arity {{ Type }}) t\
    (minductive "forest2" tt (arity {{ Type }}) f\
      (mblock [
        [constructor "node2" (arity {{ lp:f -> lp:t }})],
        [constructor "empty2" (arity f),
         constructor "cons2" (arity {{ lp:t -> lp:f -> lp:f }})]
      ]))),
  std.assert-ok! (coq.typecheck-indt-decl Tree2Decl) "tree2 declaration illtyped",
  coq.env.add-indt Tree2Decl _,

  PTree2Decl = (parameter "A" explicit {{ Type }} a\
    (minductive "ptree2" tt (arity {{ Type }}) t\
    (minductive "pforest2" tt (arity {{ Type }}) f\
      (mblock [
        [constructor "pnode2" (arity {{ lp:a -> lp:f -> lp:t }})],
        [constructor "pempty2" (arity f),
         constructor "pcons2" (arity {{ lp:t -> lp:f -> lp:f }})]
      ])))),
  std.assert-ok! (coq.typecheck-indt-decl PTree2Decl) "ptree2 declaration illtyped",
  coq.env.add-indt PTree2Decl _,

  Even2Decl = (minductive "even2" tt (arity {{ nat -> Type }}) even\
    (minductive "odd2" tt (arity {{ nat -> Type }}) odd\
      (mblock [
        [constructor "evenO2" (arity {{ lp:even 0 }}),
         constructor "evenS2" (parameter "n" explicit {{ nat }} n\
           arity {{ lp:odd lp:n -> lp:even (S lp:n) }})],
        [constructor "oddS2" (parameter "n" explicit {{ nat }} n\
           arity {{ lp:even lp:n -> lp:odd (S lp:n) }})]
      ]))),
  std.assert-ok! (coq.typecheck-indt-decl Even2Decl) "even2 declaration illtyped",
  coq.env.add-indt Even2Decl _.
}}.
Module Generated.
  Elpi test_mutind.
End Generated.

Universe tree2_u ptree2_arg_u ptree2_u even2_u.

Module Type GeneratedMutualInductives.
  Inductive tree2 : Type@{tree2_u} :=
  | node2 (f : forest2)
  with forest2 : Type@{tree2_u} :=
  | empty2
  | cons2 (t : tree2) (f : forest2).

  Inductive ptree2 (A : Type@{ptree2_arg_u}) : Type@{ptree2_u} :=
  | pnode2 (x : A) (f : pforest2 A)
  with pforest2 (A : Type@{ptree2_arg_u}) : Type@{ptree2_u} :=
  | pempty2
  | pcons2 (t : ptree2 A) (f : pforest2 A).

  Inductive even2 : nat -> Type@{even2_u} :=
  | evenO2 : even2 0
  | evenS2 n : odd2 n -> even2 (S n)
  with odd2 : nat -> Type@{even2_u} :=
  | oddS2 n : even2 n -> odd2 (S n).
End GeneratedMutualInductives.

Module GeneratedMatches <: GeneratedMutualInductives := Generated.
