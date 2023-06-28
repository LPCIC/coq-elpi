# Coercion

The `coercion` predicate enables to program Coq coercions in Elpi.

## Example of `coercion`

```coq
From elpi.apps Require Import coercion.

Elpi Accumulate coercion.db lp:{{

coercion _ {{ true }} {{ bool }} {{ Prop }} {{ True }}.
coercion _ {{ false }} {{ bool }} {{ Prop }} {{ False }}.

}}.
Elpi Typecheck coercion.

Check true : Prop.
Check false : Prop.
```

## Inspecting already declared coercions

To inspect already declared coercions, do

```Coq
Elpi Print coercion "filename.html" "coercion".
```

then open filename.html with a browser and filter predicate "coercion"
(using textbox on top left corner).


## Status

This app is experimental.
