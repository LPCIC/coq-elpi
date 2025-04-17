From elpi Require Import elpi.

Elpi Command elaborate.

(****** elaborate *******************************)
Axiom T1 : Type.
Axiom T2 : nat -> Type.
Axiom T3 : nat -> Type.

Axiom f1 : T1 -> Type.
Axiom f3 : forall b, T3 b -> Type.

Axiom g1 : T1 -> nat -> nat.
Axiom g3 : forall b, T3 b -> nat -> nat.

Axiom h : forall n , T2 n -> T3 n.

Coercion f1 : T1 >-> Sortclass.
Coercion f3 : T3 >-> Sortclass.
Coercion g1 : T1 >-> Funclass.
Coercion g3 : T3 >-> Funclass.
Coercion h : T2 >-> T3.

Elpi Query lp:{{

  std.assert-ok! (coq.elaborate-skeleton {{ fun n (t : T2 n) (x : t) => t 3 }} TY E) "that was easy",
  coq.env.add-const "elab_1" E TY tt _

}}.

Class foo (n : nat).
Definition bar n {f : foo n} := n = n.
#[local] Instance xxx : foo 3. Defined.

Elpi Query lp:{{

  std.assert-ok! (coq.elaborate-ty-skeleton {{ bar _ }} TY E) "that was easy",
  coq.env.add-const "elab_2" E (sort TY) tt _

}}.

Structure s := { field : Type; #[canonical=no] op : field -> field; }.
Canonical c := {| field := nat; op := (fun x => x) |}.

Elpi Query lp:{{

  std.assert-ok! (coq.elaborate-skeleton {{ op _ 3 }} TY E) "that was easy",
  coq.env.add-const "elab_3" E TY tt _

}}.

(* #[arguments(raw)] *)
Elpi Command test.API2.

Elpi Accumulate lp:{{
  main [indt-decl D] :- coq.say "raw:" D,
    std.assert-ok! (coq.elaborate-indt-decl-skeleton D D1) "illtyped",
    coq.say "elab1:" D1,
    coq.env.add-indt D1 I,
    coq.env.indt-decl I D2,
    coq.say "elab2:" D2.
  main [const-decl N (some BO) TYA] :- std.do! [
    coq.arity->term TYA TY,
    std.assert-ok! (coq.elaborate-ty-skeleton TY _ TY1) "illtyped",
    std.assert-ok! (coq.elaborate-skeleton BO TY1 BO1) "illtyped",
    coq.env.add-const N BO1 TY1 @transparent! _,
  ].
}}.


Elpi test.API2 Inductive ind1 (A : T1) | (B : Type) :=
  K1 : ind1 B -> ind1 B | K2 : A -> ind1 B | K3 (a : A) : ind1 B.

(*

parameter A explicit (global (const «T1»)) c0 \
 inductive ind1 tt 
  (parameter B explicit (sort (typ X0)) c1 \ arity (sort (typ X1))) c1 \
  [constructor K1 
    (parameter B explicit (sort (typ X2)) c2 \
      arity (prod `_` (app [c1, c2]) c3 \ app [c1, c2])), 
   constructor K2 
    (parameter B explicit (sort (typ X3)) c2 \
      arity (prod `_` c0 c3 \ app [c1, c2])), 
   constructor K3 
    (parameter B explicit (sort (typ X4)) c2 \
      arity (prod `a` c0 c3 \ app [c1, c2]))]
0 out of (_ : _UNBOUND_REL_3 _UNBOUND_REL_2 _UNBOUND_REL_1)
0 out of (_ : _UNBOUND_REL_2)
0 out of (_ : _UNBOUND_REL_2)
(A : T1) (B : Type) |- Type
 |- (_UNBOUND_REL_3 _UNBOUND_REL_2 _UNBOUND_REL_1 ->
 _UNBOUND_REL_4 _UNBOUND_REL_3 _UNBOUND_REL_2)
 |- (_UNBOUND_REL_2 -> _UNBOUND_REL_4 _UNBOUND_REL_3 _UNBOUND_REL_2)
 |- (_UNBOUND_REL_2 -> _UNBOUND_REL_4 _UNBOUND_REL_3 _UNBOUND_REL_2)
all params = 2, uniform params = 2
parameter A explicit (global (const «T1»)) c0 \
 parameter B explicit (sort (typ «test_API.23)»)) c1 \
  inductive ind1 tt (arity (sort (typ «test_API.25)»))) c2 \
   [constructor K1 (arity (prod `_` c2 c3 \ c2)), 
    constructor K2 
     (arity (prod `_` (app [global (const «f1»), c0]) c3 \ c2)), 
    constructor K3 
     (arity (prod `_` (app [global (const «f1»), c0]) c3 \ c2))]



elab 

(A : T1) (B : Type) |- Type
(_ : _UNBOUND_REL_3 _UNBOUND_REL_2 _UNBOUND_REL_1) |- (_UNBOUND_REL_4 _UNBOUND_REL_3 _UNBOUND_REL_2)
(_ : _UNBOUND_REL_2) |- (_UNBOUND_REL_4 _UNBOUND_REL_3 _UNBOUND_REL_2)
(a : _UNBOUND_REL_2) |- (_UNBOUND_REL_4 _UNBOUND_REL_3 _UNBOUND_REL_2)
all params = 2, uniform params = 1
parameter A explicit (global (const «T1»)) c0 \
 inductive ind1 tt 
  (parameter B explicit (sort (typ «test_API.20)»)) c1 \
    arity (sort (typ «test_API.4))»))) c1 \
  [constructor K1 
    (parameter _ explicit (app [,, c0, c1]) c2 \
      arity (app [c2, (fun `_` (sort prop) c3 \ c1), c0])), 
   constructor K2 
    (parameter _ explicit (app [global (const «f1»), c0]) c2 \
      arity (app [c2, (fun `_` (sort prop) c3 \ c1), c0])), 
   constructor K3 
    (parameter a explicit (app [global (const «f1»), c0]) c2 \
      arity (app [c2, (fun `_` (sort prop) c3 \ c1), c0]))]
File "./tests/test_API.v", line 123, characters 0-120:
Error:
wrong constant:,

*)

Elpi test.API2 Record ind2 (A : T1) := {
   fld1 : A;
   fld2 : fld1 = fld1;
}.

Elpi test.API2 Record ind3 := {
  fld3 :> Type;
  fld4 : forall x : fld3, x = x;
}.

Check (forall x : ind3, x -> Prop).

Elpi test.API2 Definition def1 A := fun x : A => x.

Elpi Query lp:{{

  std.assert-ok! (coq.elaborate-skeleton {{ op lib:elpi.hole 3 }} TY E) "that was easy 2",
  coq.env.add-const "elab_4" E TY tt _

}}.

Elpi Tactic test.
Elpi Accumulate lp:{{
solve _ _ :-
  coq.term->string X S,
  X = global (indc Y),
  coq.say S.
}}.
Goal True.
Fail elpi test.
Abort.

Elpi Tactic test2.
Elpi Accumulate lp:{{
solve _ _ :-
  coq.term->string (global (indc Y)) S,
  coq.say S.
}}.
Goal True.
elpi test2.
Abort.

#[arguments(raw)] Elpi Command detype.
Elpi Accumulate lp:{{
  main [upoly-const-decl _ _ (parameter _ _ (sort (typ U)) _ as A) (upoly-decl [UL] _ _ _)] :-
    std.assert! (coq.univ.variable U UL) "wtf",
    (@keepunivs! => std.assert-ok! (coq.elaborate-arity-skeleton A _ (parameter _ _ (sort (typ V)) _)) "wtf"),
    std.assert! (U = V) "elaboration refreshes",
    coq.say U V.
}}.


Elpi detype #[universes(polymorphic)] Definition f@{u|Set < u} (x : Type@{u}) := x.

