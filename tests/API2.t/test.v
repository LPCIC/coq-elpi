From elpi Require Import elpi.

From elpi Require test_API.

Elpi Command declare.testX.
Elpi Accumulate Db global.db.
Elpi Accumulate lp:{{

main [str "mem", str I] :-
  std.assert! (declared I) "clause not present".
main [str "length", int I] :-
  std.findall (declared J_) L,
  std.assert! (std.length L I) "wrong number of clauses".

}}.
Elpi Typecheck.

Fail Elpi declare.testX "mem" "GLOBAL".
Elpi declare.testX "length" 0.

Import test_API. (* no dup *)

Elpi declare.test "mem" "GLOBAL".
Elpi declare.test "mem" "BOX".
Elpi declare.test "length" 2.

Fail Elpi declare.test "mem" "BOX.ClausesC".
Import Box.ClausesC.
Elpi declare.test "mem" "BOX.ClausesC".
Elpi declare.test "length" 3.

Elpi declare "library" "EXTRA".

(**  strategy *)
Definition x1 := 3.
Definition x2 := 3.
Strategy opaque [x2].
Definition x3 := 3.
Strategy expand [x3].

Elpi Command strategy.
Elpi Query lp:{{
  coq.locate "x1" (const X1),
  coq.locate "x2" (const X2),
  coq.locate "x3" (const X3),
  coq.strategy.get X1 (level 0),
  coq.strategy.get X2 opaque,
  coq.strategy.get X3 expand,
  coq.strategy.set [X3] (level 123),
  coq.strategy.get X3 (level 123).

}}.

Axiom P : nat -> Prop.

Elpi Command mode.
Elpi Query lp:{{
  coq.hints.add-mode {{:gref P }} "core" [mode-input],
  coq.hints.add-mode {{:gref P }} "core" [mode-ground],
  coq.hints.modes {{:gref P }} "core" M,
  std.assert! (M = [[mode-ground],[mode-input]]) "wrong modes"
}}.

Elpi Command pv.
Elpi Accumulate lp:{{

main [trm (primitive (uint63 P))] :- !, coq.say {coq.uint63->int P}.
main [trm (primitive (float64 P))] :- !, coq.say {coq.float64->float P}.
main X :- coq.error "not a primitive-value" X.

}}.
Elpi Typecheck.

Elpi Command vp.
Elpi Accumulate lp:{{

main [int I] :- !, coq.say {coq.int->uint63 I}.
main [] :- !, coq.say {coq.float->float64 1.2}.

}}.
Elpi Typecheck.

From Coq Require Import PrimFloat Uint63.

Open Scope uint63_scope.

Elpi pv (1).
Fail Elpi pv (4611686018427387904). (* max_int + 1 *)
Elpi vp 1.
Fail Elpi vp -1.

Open Scope float_scope.

Elpi pv (1.0).
Elpi vp.

Elpi Query lp:{{

  coq.option.available? ["Primitive", "Projections"] ff

}}.

Elpi Query lp:{{

  coq.option.set ["Primitive", "Projections"] (coq.option.bool tt),
  coq.option.get ["Primitive", "Projections"] (coq.option.bool tt),
  coq.option.set ["Primitive", "Projections"] (coq.option.bool ff),
  coq.option.get ["Primitive", "Projections"] (coq.option.bool ff)

}}.

Fail Elpi Query lp:{{
  
  coq.option.add ["Primitive", "Projections"] (coq.option.bool ff) _

}}.

Elpi Query lp:{{
  
  % done in test_API.v
  % coq.option.add ["Foo", "Bar"] (coq.option.string (some "x")) tt,
  coq.option.get ["Foo", "Bar"] (coq.option.string (some "x"))

}}.

Set Foo Bar "y".

Elpi Query lp:{{
  
  coq.option.get ["Foo", "Bar"] (coq.option.string (some "y"))

}}.

Unset Foo Bar.

Elpi Query lp:{{
  
  coq.option.get ["Foo", "Bar"] (coq.option.string none)

}}.

(* Hints transparent *)

#[local] Hint Opaque plus : core.
Definition times := plus.
#[local] Hint Transparent times : core.

Elpi Query lp:{{

  {{ plus }} = global (const C1),
  coq.hints.opaque C1 "core" X1,
  std.assert!(X1 = @opaque!) "wrong opaque plus",
  {{ times }} = global (const C2),
  coq.hints.opaque C2 "core" X2,
  std.assert!(X2 = @transparent!) "wrong opaque times"

}}.

Definition x := 3.

Elpi Query lp:{{
  std.do! [
    {{ x }} = global (const C1),
    coq.hints.opaque C1 "core" @opaque!,
    coq.hints.set-opaque C1 "core" @transparent!,
    coq.hints.opaque C1 "core" @transparent!,
  ]

}}.

#[local] Hint Opaque x : core.

Elpi Query lp:{{
  std.do! [coq.env.begin-module "xx" none, coq.env.end-module XX, coq.env.import-module XX ]
}} lp:{{
  std.do! [
    {{ x }} = global (const C1),
    coq.hints.opaque C1 "core" @opaque!,
    coq.env.begin-module "xx" _,
    @local! => coq.hints.set-opaque C1 "core" @transparent!,
    coq.env.end-module M,
    coq.hints.opaque C1 "core" @opaque!,
    coq.env.import-module M,
    coq.hints.opaque C1 "core" @opaque!,
  ]

}}.

Elpi Query lp:{{
  std.do! [coq.env.begin-module "xx2" none, coq.env.end-module XX, coq.env.import-module XX]
}} lp:{{
  std.do! [
    {{ x }} = global (const C1),
    coq.hints.opaque C1 "core" @opaque!,
    coq.env.begin-module "xx2" _,
    coq.hints.set-opaque C1 "core" @transparent!,
    coq.env.end-module M,
    coq.hints.opaque C1 "core" @opaque!,
    coq.env.import-module M,
    coq.hints.opaque C1 "core" @transparent!,
  ]

}}.

#[local] Hint Opaque x : core.

Elpi Query lp:{{
    std.do! [coq.env.begin-module "xx3" none, coq.env.end-module _]
}} lp:{{
  std.do! [
    {{ x }} = global (const C1),
    coq.hints.opaque C1 "core" @opaque!,
    coq.env.begin-module "xx3" _,
    @global! => coq.hints.set-opaque C1 "core" @transparent!,
    coq.env.end-module M,
    coq.hints.opaque C1 "core" @transparent!,
  ]

}}.
Fail Elpi Query lp:{{

  {{ x }} = global (const C1),
  coq.hints.opaque C1 "corexx" T

}}.


(* Hints transparent *)

Definition xeq T x y := x = y :> T.
Axiom xxx : xeq _ 0 1.

Elpi Query lp:{{
 coq.hints.add-resolve {{:gref xxx }} "core" 0 _.
}}.

Goal 0 = 1. Fail solve [trivial]. Abort.

Create HintDb xxx.

Elpi Query lp:{{
 coq.hints.add-resolve {{:gref xxx }} "xxx" 0 {{ 0 = _ }}
}}.

Print HintDb xxx.
(* I could not test the pattern, but it is printed
Goal 0 = 1. solve [debug eauto with xxx]. Abort.
*)

(* ------------- functor application ---------------- *)

(*Module Type T. Axiom Inline(1) T : Type. End T.*)
Elpi Query lp:{{
  std.do! [ coq.env.begin-module-type "T", coq.env.end-module-type _, ]
}} lp:{{
  coq.env.begin-module-type "T",
  @inline-at! 1 => coq.env.add-axiom "T" {{ Type }} _,
  coq.env.end-module-type _

}}.

(*Module F(P : T). Definition id (a : P.T) := a. End F.*)
Elpi Query lp:{{
  std.do! [coq.env.begin-module-functor "F" none [pr "P" {coq.locate-module-type "T"}], coq.env.end-module _]
}} lp:{{
  coq.env.begin-module-functor "F" _ _,
  coq.locate "P.T" GR,
  coq.env.add-const "id" (fun `a` (global GR) a\ a) _ _ _,
  coq.env.end-module _.

}}.

(*Module X. Definition T := nat. End X.*)
Elpi Query lp:{{
  std.do! [coq.env.begin-module "X" none, coq.env.end-module _]
}} lp:{{

  coq.env.begin-module "X" _,
  coq.env.add-const "T" {{ nat }} _ _ _,
  coq.env.end-module _.

}}.

(*Module G := F X [no inline].*)
Elpi Query lp:{{
  std.do! [coq.env.apply-module-functor "G" none {coq.locate-module "F"} [{coq.locate-module "X"}] coq.inline.no _]
}} lp:{{
  coq.env.apply-module-functor "G" _ _ _ _ G,
  coq.say G
}}.
Print Module G.

(*Module H := F X [inline at leve 2].*)
Elpi Query lp:{{
  std.do! [coq.env.apply-module-functor "H" none {coq.locate-module "F"} [{coq.locate-module "X"}] (coq.inline.at 2) _]
}} lp:{{
  coq.env.apply-module-functor "H" _ _ _ _ H,
  coq.say H
}}.
Print Module H.

Goal G.id 3%nat = 3%nat.
Fail match goal with |- @Logic.eq nat _ _ => idtac end.
match goal with |- @Logic.eq X.T _ _ => idtac end.
Abort.

Goal H.id 3%nat = 3%nat.
match goal with |- @Logic.eq nat _ _ => idtac end.
Fail match goal with |- @Logic.eq X.T _ _ => idtac end.
Abort.

(* ------------- functor type application ---------------- *)

(*Module Type FT (P : T). Axiom idT : P.T -> P.T. End FT.*)
Elpi Query lp:{{
  std.do! [coq.env.begin-module-type-functor "FT" [pr "P" {coq.locate-module-type "T"}], coq.env.end-module-type _]
}} lp:{{

  coq.env.begin-module-type-functor "FT" _,
  coq.locate "P.T" GR,
  coq.env.add-axiom "idT" (prod _ (global GR) _\ (global GR)) _,
  coq.env.end-module-type _.

}}.
Print Module Type FT.

(*Module Type GT := FT X [no inline].*)
Elpi Query lp:{{
  std.do! [coq.env.apply-module-type-functor "GT" {coq.locate-module-type "FT"} [{coq.locate-module "X"}] coq.inline.no _]
}} lp:{{
  coq.env.apply-module-type-functor "GT" _ _ _ G,
  coq.say G
}}.
Print Module Type GT.

(*Module Type HT := FT X [inline at leve 2].*)
Elpi Query lp:{{
  std.do! [coq.env.apply-module-type-functor "HT" {coq.locate-module-type "FT"} [{coq.locate-module "X"}] (coq.inline.at 2) _]
}} lp:{{
  coq.env.apply-module-type-functor "HT" _ _ _ H,
  coq.say H
}}.
Print Module Type HT.

Module Test (X : GT) (Y : HT).

Goal X.idT 3%nat = 3%nat.
Fail match goal with |- @Logic.eq nat _ _ => idtac end.
match goal with |- @Logic.eq X.T _ _ => idtac end.
Abort.

Goal Y.idT 3%nat = 3%nat.
match goal with |- @Logic.eq nat _ _ => idtac end.
Fail match goal with |- @Logic.eq X.T _ _ => idtac end.
Abort.

End Test.

Elpi Query lp:{{

   coq.univ.variable.of-term (prod `_` (sort (typ U)) _\ sort (typ V)) S,
   coq.univ.variable U UV,
   coq.univ.variable V VV,
   coq.univ.variable.set.elements S L,
   ( L = [UV,VV] ; L = [VV,UV] )
   
}}.
(**********************************************)

Elpi Command test.eta.
Elpi Accumulate lp:{{
  test T1 T2 :-
    coq.reduction.eta-contract T1 X,  
    Msg is {coq.term->string T1} ^ "\n--eta-->\n" ^ {coq.term->string X} ^ "\n!=\n" ^ {coq.term->string T2} ^ "\n\n",
    std.assert! (X = T2) Msg.
}}.
Elpi Query lp:{{
   std.do! [
     test {{ fun x => x }} {{ fun x => x }},
     test {{ fun x => S x }} {{ S }},
     test {{ fun x y => plus x y }} {{ plus }},
     test {{ fun x y => x x y }} {{ fun x y => x x y }},
     test {{ fun z => S (fun x y => plus x y) z }} {{ S plus }},
     test {{ fun z => S (fun x y => z x y) }} {{ S }},
     test {{ fun z => S (fun x y => z z x y) }} {{ fun z => S (z z) }},
   ].
}}.
