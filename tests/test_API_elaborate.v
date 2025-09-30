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

Elpi Query lp:{{/*(*/

  std.assert-ok! (coq.elaborate-skeleton {{ fun n (t : T2 n) (x : t) => t 3 }} TY E) "that was easy",
  coq.env.add-const "elab_1" E TY tt _

/*)*/}}.

Class foo (n : nat).
Definition bar n {f : foo n} := n = n.
#[local] Instance xxx : foo 3. Defined.

Elpi Query lp:{{/*(*/

  std.assert-ok! (coq.elaborate-ty-skeleton {{ bar _ }} TY E) "that was easy",
  coq.env.add-const "elab_2" E (sort TY) tt _

/*)*/}}.

Structure s := { field : Type; #[canonical=no] op : field -> field; }.
Canonical c := {| field := nat; op := (fun x => x) |}.

Elpi Query lp:{{/*(*/

  std.assert-ok! (coq.elaborate-skeleton {{ op _ 3 }} TY E) "that was easy",
  coq.env.add-const "elab_3" E TY tt _

/*)*/}}.

(* #[arguments(raw)] *)
Elpi Command test.API2.

Elpi Accumulate lp:{{/*(*/
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
/*)*/}}.


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

Elpi Query lp:{{/*(*/

  std.assert-ok! (coq.elaborate-skeleton {{ op lib:elpi.hole 3 }} TY E) "that was easy 2",
  coq.env.add-const "elab_4" E TY tt _

/*)*/}}.

Elpi Tactic test.
Elpi Accumulate lp:{{/*(*/
solve _ _ :-
  coq.term->string X S,
  X = global (indc Y),
  coq.say S.
/*)*/}}.
Goal True.
Fail elpi test.
Abort.

Elpi Tactic test2.
Elpi Accumulate lp:{{/*(*/
solve _ _ :-
  coq.term->string (global (indc Y)) S,
  coq.say S.
/*)*/}}.
Goal True.
elpi test2.
Abort.

#[arguments(raw)] Elpi Command detype.
Elpi Accumulate lp:{{/*(*/
  main [upoly-const-decl _ _ (parameter _ _ (sort (typ U)) _ as A) (upoly-decl [UL] _ _ _)] :-
    std.assert! (coq.univ.variable U UL) "wtf",
    (@keepunivs! => std.assert-ok! (coq.elaborate-arity-skeleton A _ (parameter _ _ (sort (typ V)) _)) "wtf"),
    std.assert! (U = V) "elaboration refreshes",
    coq.say U V.
/*)*/}}.


Elpi detype #[universes(polymorphic)] Definition f@{u|Set < u} (x : Type@{u}) := x.

(** Parser tests *)
Succeed #[arguments(raw)] Elpi Command argtest.
Succeed #[arguments(unelaborated)] Elpi Command argtest.
Succeed #[arguments(elaborated)] Elpi Command argtest.
Succeed #[arguments(syntactic)] Elpi Command argtest.
(* The test below should fail but does not for some reason.
   Also, the error message is terribly. See https://github.com/rocq-prover/rocq/issues/17041 *)
#[local] Set Warnings "+unsupported-attributes".
Succeed #[arguments(something_else)] Elpi Command argtest.

(* Arguments do not allow any specified values, not even booleans *)
Fail #[arguments(raw="test")] Elpi Command detype.
Fail #[arguments(raw=false)] Elpi Command detype.

(* Syntactic tests *)
#[arguments(syntactic)] Elpi Command syntax_test1.
Elpi Accumulate lp:{{/*(*/
  main [syntactic.arg (syntactic.int 1)].
/*)*/}}.
Elpi syntax_test1 1.
Fail Elpi syntax_test1 2.

#[arguments(syntactic)] Elpi Command syntax_test2.
Elpi Accumulate lp:{{/*(*/
  main [syntactic.arg (syntactic.str "test")].
/*)*/}}.
Elpi syntax_test2 "test".
Fail Elpi syntax_test2 "foo".

#[arguments(syntactic)] Elpi Command syntax_test3.
Elpi Accumulate lp:{{/*(*/
  main [syntactic.arg Arg] :-
  syntactic.default-elab Arg (int 1) ok.
/*)*/}}.
Elpi syntax_test3 1.
Fail Elpi syntax_test3 2.

#[arguments(syntactic)] Elpi Command syntax_test4.
Elpi Accumulate lp:{{/*(*/
  main [syntactic.arg Arg] :-
  syntactic.default-elab Arg (trm {{(1 + 1)}}) ok.
/*)*/}}.
Elpi syntax_test4 (1 + 1).
Fail Elpi syntax_test4 (2 + 1).


(* Test evar dependencies *)
#[arguments(elaborated)] Elpi Command evar_deps.
Elpi Accumulate lp:{{/*(*/
  main [trm T1, trm T2] :-
   pattern_match T1 {{ 1 + 1 }},
   pattern_match T2 {{ 1 }}.
/*)*/}}.
(* Evars are elaborated/interpreted  before they are unified during the execution of [main]. *)
Elpi evar_deps (?[x] + ?x) (?x).
(* Rocq is perhaps a bit too eager to throw away instantiated evars: https://github.com/rocq-prover/rocq/issues/21116 *)
Fail Elpi evar_deps (eq_refl : (?[x] = 1)) (?x).

#[arguments(syntactic)] Elpi Command syntax_test_evars.
Elpi Accumulate lp:{{/*(*/
  main [syntactic.arg Arg1, syntactic.arg Arg2] :-
  syntactic.default-elab Arg1 (trm {{ 1 + 1 }}) ok,
  syntactic.default-elab Arg2 (trm {{(1)}}) ok.
/*)*/}}.
Elpi syntax_test_evars (1 + 1) (1).
Elpi syntax_test_evars (?[x] + 1) (1).
Elpi syntax_test_evars (1 + 1) (?[x]).
(* Our program interpretes and then unifies the evars in the first argument
before it interpretes the second argument. The named evar disappears after the
first step and thus the second argument cannot be interpreted any more. *)
Fail Elpi syntax_test_evars (?[x] + ?x) (?x).

(* We can fix this by taking these steps more slowly. *)
#[arguments(syntactic)] Elpi Command syntax_test_evars_staged.
Elpi Accumulate lp:{{/*(*/
  main [syntactic.arg Arg1, syntactic.arg Arg2] :-
  syntactic.default-elab Arg1 (trm T1) ok,
  syntactic.default-elab Arg2 (trm T2) ok,
  T1 = {{ 1 + 1 }},
  T2 = {{ 1 }}.
/*)*/}}.
Elpi syntax_test_evars_staged (1 + 1) (1).
Elpi syntax_test_evars_staged (?[x] + 1) (1).
Elpi syntax_test_evars_staged (1 + 1) (?[x]).
(* Now we interprete both terms first and only then start unifying them. *)
Elpi syntax_test_evars_staged (?[x] + ?x) (?x).


(* Adding scopes to syntactic terms. *)
Declare Scope test_scope.
Delimit Scope test_scope with test.
Notation "'[test_notation' ]" := (tt) : test_scope.

#[arguments(syntactic)] Elpi Command syntax_test6.
Elpi Accumulate lp:{{/*(*/
  main [syntactic.arg (syntactic.str Scope), syntactic.arg (syntactic.trm Arg1)] :-
  syntactic.push-scope Arg1 syntactic.delimit-only-tmp-scope Scope ScopedArg,
  syntactic.default-elab (syntactic.trm ScopedArg) (trm {{ tt }}) ok.
/*)*/}}.
Fail Check [test_notation].
Fail Elpi syntax_test6 "core" ([test_notation ]).
Succeed Check [test_notation]%test.
Elpi syntax_test6 "test" ([test_notation ]).

(* Manual Elaboration *)

#[arguments(syntactic)] Elpi Command elaborate_test.
Elpi Accumulate lp:{{/*(*/
  main [syntactic.arg (syntactic.trm T)] :-
  syntactic.elaborate T without-type-constraint T' ok,
  T' = {{ _ + _ }}.
/*)*/}}.
Elpi elaborate_test (1 + 1).
Elpi elaborate_test (1 + ?[x]).
Elpi elaborate_test (?[x] + ?x).

Definition f : unit -> nat := fun _ => 0.
Coercion f : unit >-> nat.

Class Cls := { proj : nat }.
Instance : Cls := {| proj := 1 |}.

Elpi elaborate_test (1 + tt).     (* coercions *)
Elpi elaborate_test (tt + 1).
Elpi elaborate_test (tt + proj).  (* and typeclasses *)
Elpi elaborate_test (proj + tt).

#[arguments(syntactic)] Elpi Command elaborate_test_ty.
Elpi Accumulate lp:{{/*(*/
  main [syntactic.arg (syntactic.trm Ty), syntactic.arg (syntactic.trm T)] :-
  syntactic.elaborate Ty is-type Ty' ok,
  syntactic.elaborate T (of-type Ty') T' ok,
  ground_term T'.
/*)*/}}.
Elpi elaborate_test_ty (nat) (1 + 1).
Fail Elpi elaborate_test_ty (False) (I).
Elpi elaborate_test_ty (nat) (tt). (* uses coercion *)
Elpi elaborate_test_ty (nat) (proj). (* typeclasses *)
Elpi elaborate_test_ty (Cls -> nat) (@proj).

#[arguments(syntactic)] Elpi Command elaborate_test_ty2.
Elpi Accumulate lp:{{/*(*/
  main [syntactic.arg (syntactic.trm Ty), syntactic.arg (syntactic.trm T)] :-
  syntactic.elaborate Ty is-type Ty' ok,
  (@no-tc! => @no-coercion! => syntactic.elaborate T (of-type Ty') T' ok),
  ground_term T'.
/*)*/}}.
Elpi elaborate_test_ty2 (nat) (1 + 1).
Fail Elpi elaborate_test_ty (False) (I).
Fail Elpi elaborate_test_ty2 (nat) (tt). (* requires coercions *)
Fail Elpi elaborate_test_ty2 (nat) (proj). (* requires TC *)
Elpi elaborate_test_ty2 (Cls -> nat) (@proj).

(* Error messages *)
#[arguments(syntactic)] Elpi Command error_msgs.
Elpi Accumulate lp:{{/*(*/
  main [syntactic.arg (syntactic.str RegExp), syntactic.arg (syntactic.trm T)] :-
  syntactic.elaborate T without-type-constraint _ (error E),
  rex.match RegExp E.
/*)*/}}.
Elpi error_msgs ".*has type.*True.*" (I + 1).
Elpi error_msgs ".*exhaust.*false.*" (match true with | true => I end).
