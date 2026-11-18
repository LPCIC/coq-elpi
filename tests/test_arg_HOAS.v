

From elpi Require Import elpi.

Elpi Command declarations.
Elpi Accumulate lp:{{

main [indt-decl A] :- !, std.spy-do! [
  coq.say "raw:" A,
  std.assert-ok! (coq.typecheck-indt-decl A) "Illtyped inductive declaration",
  coq.say "typed:" A,
  coq.env.add-indt A _,
].
main [upoly-indt-decl A UD] :- !, std.spy-do! [
  coq.say "raw:" A UD,
  coq.univ.print,
  std.assert-ok! (coq.typecheck-indt-decl A) "Illtyped inductive declaration",
  coq.say "typed:" A,
  coq.upoly-decl->attribute UD CL,
  CL => coq.env.add-indt A _,
].
main [const-decl N (some BO) A] :- !, std.spy-do! [
  coq.arity->term A TY,
  std.assert-ok! (coq.typecheck BO TY) "illtyped definition",
  coq.env.add-const N BO TY _ _,
].
 main [upoly-const-decl N (some BO) A UD] :- !, std.spy-do! [
  coq.arity->term A TY,
  std.assert-ok! (coq.typecheck BO TY) "illtyped definition",
  coq.upoly-decl->attribute UD CL,
  CL => coq.env.add-const N BO TY _ _,
].
main [const-decl N none A] :- !, std.spy-do! [
  coq.arity->term A TY,
  std.assert-ok! (coq.typecheck-ty TY _) "illtyped axiom",
  coq.env.add-axiom N TY _,
].
main [upoly-const-decl N none A UD] :- !, std.spy-do! [
  coq.arity->term A TY,
  std.assert-ok! (coq.typecheck-ty TY _) "illtyped axiom",
  coq.upoly-decl->attribute UD CL,
  CL => coq.env.add-axiom N TY _,
].

main [ctx-decl (context-item "T" _ _ none t\
                context-item "x" _ t none _\
                context-item "l" _ _ (some _) _\
                context-end)].

main Args :- coq.error Args.
}}.


#[arguments(raw)]
Elpi Command raw_declarations.
Elpi Accumulate lp:{{

main [indt-decl RA] :- !, std.spy-do! [
  coq.say "raw:" RA,
  std.assert-ok! (coq.elaborate-indt-decl-skeleton RA A) "Illtyped inductive declaration",
  coq.say "typed:" A,
  coq.env.add-indt A _,
].
main [upoly-indt-decl RA UD] :- !, std.spy-do! [
  coq.say "raw:" RA UD,
  coq.univ.print,
  @keepunivs! => std.assert-ok! (coq.elaborate-indt-decl-skeleton RA A) "Illtyped inductive declaration",
  coq.say "typed:" A,
  coq.upoly-decl->attribute UD CL,
  CL => coq.env.add-indt A _,
].
main [const-decl N (some RBO) RA] :- !, std.spy-do! [
  coq.arity->term RA RTY,
  std.assert-ok! (coq.elaborate-ty-skeleton RTY _ TY) "illtyped arity", 
  std.assert-ok! (coq.elaborate-skeleton RBO TY BO) "illtyped definition",
  coq.env.add-const N BO TY _ _,
].
main [upoly-const-decl N (some RBO) RA UD] :- !, std.spy-do! [
  coq.arity->term RA RTY,
  @keepunivs! => std.assert-ok! (coq.elaborate-ty-skeleton RTY _ TY) "illtyped arity", 
  @keepunivs! => std.assert-ok! (coq.elaborate-skeleton RBO TY BO) "illtyped definition",
  coq.upoly-decl->attribute UD CL,
  CL => coq.env.add-const N BO TY _ _,
].
main [const-decl N none RA] :- !, std.spy-do! [
  coq.arity->term RA RTY,
  std.assert-ok! (coq.elaborate-ty-skeleton RTY _ TY) "illtyped axiom",
  coq.env.add-axiom N TY _,
].
main [upoly-const-decl N none RA UD] :- !, std.spy-do! [
  coq.arity->term RA RTY,
  @keepunivs! => std.assert-ok! (coq.elaborate-ty-skeleton RTY _ TY) "illtyped axiom",
  coq.upoly-decl->attribute UD CL,
  CL => coq.env.add-axiom N TY _,
].

main [ctx-decl (context-item "T" _ _ none t\
                context-item "x" _ t none _\
                context-item "l" _ _ (some _) _\
                context-end)].

main Args :- coq.error Args.
}}.


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

Module more_nup.
Inductive t (A : Type) (y : nat) : Type :=
  | K (x : A) {n : nat} : t A n -> t A y.

(* issue #383 *)
Elpi Query lp:{{
  coq.locate "t" (indt I),
  coq.env.indt-decl I D,
  std.assert! (D =
    parameter "A" explicit (sort (typ _)) c0 \
     inductive "t" tt 
       (parameter "y" explicit (global (indt _)) c1 \
	        arity (sort (typ _))) c1 \
      [constructor "K" 
        (parameter "y" explicit (global (indt _)) c2 \
          parameter "x" explicit c0 c3 \
          parameter "n" maximal (global (indt _)) c4 \
            arity (prod `_` (app [c1, c4]) c5 \ app [c1, c2]))]) "wrong HOAS nup".
}}.

End more_nup.

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

Module record_attributes0.
Record foo A (B : A) : Type := {
    a (_: A) (_ : A) : A;
    z (a : A) :>  B = B -> A;
#[canonical=no]
    x (w := 3) : forall x, a x x = x;
  }.
Elpi Query lp:{{
  coq.locate "foo" (indt I),
  coq.env.projections I [some A, some B, some C],
  coq.CS.canonical-projection? A,
  coq.CS.canonical-projection? B,
  not (coq.CS.canonical-projection? C).
}}.
End record_attributes0.


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
  coq.env.projections I [some A, some B, some C],
  coq.CS.canonical-projection? A,
  coq.CS.canonical-projection? B,
  not (coq.CS.canonical-projection? C).
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
     (field [coercion reversible,canonical tt] "f" (prod `_` c0 _\ c0) c2\
      field [coercion off,canonical tt] "g" c0 c3\
      field [coercion off,canonical tt] "p" (app [global (indt _), c0, c1, c3]) _\
      end-record)) "not a record",
  coq.env.add-indt R _.
}}.

Print r.
End copy.

Set Printing Universes.

(*****************************************)

Elpi declarations #[universes(template=no)] Inductive X1 : Type := .
Fail Elpi declarations #[universes(template)] Inductive X2 : Type := .
About X1.

Fail Elpi Query lp:{{ coq.locate "X1" GR, coq.env.global GR (pglobal GR _) }}.

(*****************************************)

Elpi declarations #[universes(polymorphic)] Inductive X3 : Type := .
Elpi declarations #[universes(polymorphic,cumulative)] Inductive X4 : Type := .
About X3.
About X4.

Elpi Query lp:{{ coq.locate "X3" GR, coq.env.global GR (pglobal GR _) }}.
Elpi Query lp:{{ coq.locate "X4" GR, coq.env.global GR (pglobal GR _) }}.

Elpi declarations #[universes(polymorphic)] Inductive X5@{u} : Type@{u} := .
About X5.

Elpi declarations #[universes(polymorphic)] Inductive X6@{u v|u<v} : Type@{v} := K (u : Type@{u}).
About X6.

Fail Elpi raw_declarations #[universes(polymorphic)] Inductive X7@{u v|u<v} : Type@{v} := K (u : Type@{u}).

Elpi raw_declarations #[universes(polymorphic)] Inductive X8 : Type := .
About X8.

(* ******************** *)
Elpi declarations #[universes(polymorphic)] Definition f1 (T:Type) (x:T) := x.
About f1.

Elpi declarations #[universes(polymorphic)] Definition f2@{u} (T:Type@{u}) (T1:Type@{u}) (x:T) := x.
About f2.

Elpi raw_declarations #[universes(polymorphic)] Definition f3 (T:Type) (x:T) := x.
About f3.

Elpi raw_declarations #[universes(polymorphic)] Definition f4@{u} (T:Type@{u}) (T1:Type@{u}) (x:T) := x.
About f4.

Universe uuu.

Elpi raw_declarations Definition f5 (T:Type@{uuu}) (T1:Type@{uuu}) (x:T) := x.
Fail Elpi declarations Definition f6@{uuux} (T:Type@{uuu}) (T1:Type@{uuux}) (x:T) := x.
Fail Elpi raw_declarations Definition f6@{uuux} (T:Type@{uuu}) (T1:Type@{uuux}) (x:T) := x.

Set Universe Polymorphism.
Elpi declarations Definition f6@{uuux} (T:Type@{uuu}) (T1:Type@{uuux}) (x:T) := x.
About f6.

Fail Elpi declarations Definition f7 := f6@{Prop}.
Fail Elpi raw_declarations Definition f7 := f6@{Prop}.

Elpi declarations Definition f7 := f6@{Set}.
Elpi raw_declarations Definition f8 := f6@{Set}.

Elpi declarations Definition f7' := f6@{uuu}.
Elpi raw_declarations Definition f8' := f6@{uuu}.

Elpi declarations Definition f7''@{x} := f6@{x}.
Elpi raw_declarations Definition f8''@{x} := f6@{x}.

(* ******************** *)
Unset Universe Polymorphism.

Class I := {}.
Class L (i : I) := {}.

(*#[arguments(raw)] *)
Elpi Command bug_394.
Elpi Accumulate lp:{{
  main [A,B,C] :-
    coq.say A B C,
    std.assert! (A =
      const-decl "D"
       (some (fun `i` _ c0 \ fun `l` (app [{{ L }}, c0]) c1 \ {{ True }})) 
       (parameter "i" maximal _ c0 \
         parameter "l" maximal (app [{{ L }}, c0]) c1 \
          arity (sort prop)))
      "not ok 1",
    std.assert! (B =
      const-decl "D"
       (some (fun `i` _ c0 \ fun `l` (app [{{ L }}, c0]) c1 \ {{ True }})) 
       (parameter "i" maximal _ c0 \
         parameter _ maximal (app [{{ L }}, c0]) c1 \
          arity (sort prop)))
      "not ok 2",
    std.assert! (C =
      const-decl "D"
       (some (fun `i` _ c0 \ fun `l` (app [{{ L }}, c0]) c1 \ fun _ {{nat}} c2\ {{ True }})) 
       (parameter "i" maximal _ c0 \
         parameter _ maximal (app [{{ L }}, c0]) c1 \
          parameter "n" explicit {{ nat }} c2\
           arity (sort prop)))
      "not ok 3"
      .

}}.


Elpi bug_394
  Definition D `{l : L} : Prop := True
  Definition D `{L} : Prop := True
  Definition D `{L} (n:nat) : Prop := True
  .

Elpi Tactic open.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ [open-trm N X]) _ :- coq.say N X.
}}.
Goal True.
elpi open `(x + y).
Abort.

(* coq.parse.argument *)

Declare Scope my_scope.
Delimit Scope my_scope with my.
Notation "x + y" := (Nat.sub x y) : my_scope.
Declare Scope nodelim_scope.

Elpi Query lp:{{
  coq.parse.argument "3" tt "" A1 D1,
  std.assert! (A1 = int 3, D1 = ok) "int",
  coq.parse.argument "foo.bar" ff "" A2 D2,
  std.assert! (A2 = str "foo.bar", D2 = ok) "qualid",
  coq.parse.argument "\"a b\"" ff "" A3 D3,
  std.assert! (A3 = str "a b", D3 = ok) "string",
  coq.parse.argument "(1 + 2)" ff "" A4 D4,
  std.assert! (A4 = trm {{ Nat.add 1 2 }}, D4 = ok) "term",
  coq.parse.argument "(1 + 2)" tt "" A5 D5,
  std.assert! (A5 = trm {{ Nat.add 1 2 }}, D5 = ok) "raw term",
  coq.parse.argument "(1 + 2)" ff "my" A6 D6,
  std.assert! (A6 = trm {{ Nat.sub 1 2 }}, D6 = ok) "term in scope (delimiter)",
  coq.parse.argument "(1 + 2)" tt "my_scope" A7 D7,
  std.assert! (A7 = trm {{ Nat.sub 1 2 }}, D7 = ok) "raw term in scope (name)"
}}.

Elpi Query lp:{{
  coq.parse.argument "Definition d : nat := 1" ff "" A1 D1,
  std.assert! (A1 = const-decl "d" (some {{ 1 }}) (arity {{ nat }}), D1 = ok) "definition",
  coq.parse.argument "Definition d (n : nat) := n" tt "" A2 D2,
  std.assert! (A2 = const-decl "d" (some (fun `n` {{ nat }} n\ n)) (parameter "n" explicit {{ nat }} _\ arity _), D2 = ok) "raw definition",
  coq.parse.argument "Inductive i := K" tt "" (indt-decl _) ok,
  coq.parse.argument "Inductive i := K" ff "" (indt-decl _) ok,
  coq.parse.argument "Record r := { f : nat }" ff "" (indt-decl _) ok,
  coq.parse.argument "Context (T : Type) (t : T)" ff "" (ctx-decl _) ok
}}.

(* variables bound in the elpi context *)
Elpi Query lp:{{
  pi x\ decl x `x` {{ nat }} => (
    coq.parse.argument "(x + 1)" tt "" (A1 x) ok,
    std.assert! (A1 x = trm {{ lp:x + 1 }}) "raw term with free var",
    coq.parse.argument "(x + 1)" ff "" (A2 x) ok,
    std.assert! (A2 x = trm {{ lp:x + 1 }}) "term with free var",
    coq.parse.argument "(x + 1)" ff "my" (A3 x) ok,
    std.assert! (A3 x = trm {{ Nat.sub lp:x 1 }}) "term with free var in scope",
    coq.parse.argument "Definition d := x" tt "" (A4 x) ok,
    std.assert! (A4 x = const-decl "d" (some x) _) "raw definition with free var",
    coq.parse.argument "Definition d : nat := x" ff "" (A5 x) ok,
    std.assert! (A5 x = const-decl "d" (some x) (arity {{ nat }})) "definition with free var",
    coq.parse.argument "Context (y : x = x)" ff "" (A6 x) ok,
    std.assert! (A6 x = ctx-decl (context-item "y" _ {{ lp:x = lp:x }} none _\ context-end)) "context with free var",
    coq.parse.argument "Inductive i : Prop := K : x = x -> i" tt "" (indt-decl _) ok,
    coq.parse.argument "Inductive i : Prop := K : x = x -> i" ff "" _ (error _),
    coq.parse.argument "Record r : Prop := { f : x = x }" ff "" _ (error _)
  ).
}}.

Elpi Query lp:{{
  coq.parse.argument "(1 + true)" tt "" (trm _) ok,
  std.forall [
    triple "(" ff "",
    triple "3 4" ff "",
    triple "(1 + 2)" ff "no_such_scope",
    triple "(1 + 2)" ff "nodelim_scope",
    triple "(1 + true)" ff "",
    triple "(x + 1)" tt "",
    triple "Definition d : nat := true" ff ""
  ] (x\ sigma S R Sc D M\ x = triple S R Sc,
    coq.parse.argument S R Sc _ D,
    std.assert! (D = error M, not (M = "")) S,
    coq.say S "->" D).
}}.

Elpi Tactic parse_arg.
Elpi Accumulate lp:{{
solve (goal Ctx _ _ _ [str S]) _ :-
  coq.parse.argument S ff "" A ok,
  std.assert! (A = trm (app [global _, X, _]), Ctx = [decl X _ _]) "goal context".
}}.
Goal forall n : nat, True.
intro n.
elpi parse_arg "(n + 1)".
Abort.
