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
Elpi test_mutind.

Check tree2 : Type.
Check forest2 : Type.
Check node2 : forest2 -> tree2.
Check empty2 : forest2.
Check cons2 : tree2 -> forest2 -> forest2.

Check ptree2 : Type -> Type.
Check pforest2 : Type -> Type.
Check pnode2 : forall A, A -> pforest2 A -> ptree2 A.
Check pempty2 : forall A, pforest2 A.
Check pcons2 : forall A, ptree2 A -> pforest2 A -> pforest2 A.

Check even2 : nat -> Type.
Check odd2 : nat -> Type.
Check evenO2 : even2 0.
Check evenS2 : forall n, odd2 n -> even2 (S n).
Check oddS2 : forall n, even2 n -> odd2 (S n).
