# Coercion

The `coercion` app enables to program Coq coercions in Elpi.

This app is experimental.

## The coercion predicate

The `coercion` predicate lives in the database `coercion.db`

```elpi
% [coercion Ctx V Inferred Expected Res] is queried to cast V to Res
% - [Ctx] is the context
% - [V] is the value to be coerced
% - [Inferred] is the type of [V]
% - [Expected] is the type [V] should be coerced to
% - [Res] is the result (of type [Expected])
pred coercion i:goal-ctx, i:term, i:term, i:term, o:term.
```

By addings rules for this predicate one can recover from a type error, that is
when `Inferred` and `Expected` are not unifiable.

## Simple example of coercion

This example maps `True : Prop` to `true : bool`, which is a function you
cannot express in type theory, hence in the standard Coercion system.

```coq
From elpi.apps Require Import coercion.
From Coq Require Import Bool.

Elpi Accumulate coercion.db lp:{{

coercion _ {{ True }} {{ Prop }} {{ bool }} {{ true }}.
coercion _ {{ False }} {{ Prop }} {{ bool }} {{ false }}.

}}.
Elpi Typecheck coercion. (* checks the elpi program is OK *)

Check True && False.
```

## Example of coercion with proof automation

This coercion enriches `x : T` to a `{x : T | P x}` by using
`my_solver` to prove `P x`.

```coq
From elpi.apps Require Import coercion.
From Coq Require Import Arith ssreflect.

Ltac my_solver := trivial with arith.

Elpi Accumulate coercion.db lp:{{

coercion _ X Ty {{ @sig lp:Ty lp:P }} Solution :- std.do! [
  % we unfold letins since the solver is dumb and the `as` in the second
  % example introduces a letin
  (pi a b b1\ copy a b :- def a _ _ b, copy b b1) => copy X X1,
  % we build the solution
  Solution = {{ @exist lp:Ty lp:P lp:X1 _ }},
  % we call the solver
  coq.ltac.collect-goals Solution [G] [],
  coq.ltac.open (coq.ltac.call-ltac1 "my_solver") G [],
].

}}.
Elpi Typecheck coercion.

Goal {x : nat | x > 0}.
apply: 3.
Qed.

Definition ensure_pos n : {x : nat | x > 0} :=
  match n with
  | O => 1
  | S x as y => y
  end.
```
