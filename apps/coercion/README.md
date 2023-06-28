# Coercion

The `coercion` predicate enables to program Coq coercions in Elpi.

## Example of `coercion`

```coq
From elpi.apps Require Import coercion.

Elpi Accumulate Coercion lp:{{

coercion _ {{ true }} {{ bool }} {{ Prop }} {{ True }}.
coercion _ {{ false }} {{ bool }} {{ Prop }} {{ False }}.

}}.
Elpi Typecheck Coercion.

Check true : Prop.
Check false : Prop.
```

## Requirements

Appropriate version of Coq with support for coercion hooks
https://github.com/coq/coq/pull/17794
