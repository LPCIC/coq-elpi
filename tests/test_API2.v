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

From Coq Require Import PrimFloat Int63.

Open Scope int63_scope.

Elpi pv (1).
Fail Elpi pv (4611686018427387904). (* max_int + 1 *)

Open Scope float_scope.

Elpi pv (1.0).

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

Hint Opaque plus : core.
Definition times := plus.
Hint Transparent times : core.

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

Hint Opaque x : core.

Elpi Query lp:{{
  std.do! [
    {{ x }} = global (const C1),
    coq.hints.opaque C1 "core" @opaque!,
    coq.env.begin-module "xx" none,
    @local! => coq.hints.set-opaque C1 "core" @transparent!,
    coq.env.end-module M,
    coq.hints.opaque C1 "core" @opaque!,
    coq.env.import-module M,
    coq.hints.opaque C1 "core" @opaque!,
  ]

}}.

Elpi Query lp:{{
  std.do! [
    {{ x }} = global (const C1),
    coq.hints.opaque C1 "core" @opaque!,
    coq.env.begin-module "xx2" none,
    coq.hints.set-opaque C1 "core" @transparent!,
    coq.env.end-module M,
    coq.hints.opaque C1 "core" @opaque!,
    coq.env.import-module M,
    coq.hints.opaque C1 "core" @transparent!,
  ]

}}.

Hint Opaque x : core.

Elpi Query lp:{{
  std.do! [
    {{ x }} = global (const C1),
    coq.hints.opaque C1 "core" @opaque!,
    coq.env.begin-module "xx3" none,
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
