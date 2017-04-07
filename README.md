# coq-elpi
Coq plugin embedding elpi

## Purpose
Elpi provides an easy-to-embed implementation of lambda-prolog, a programming language
well suited to express transformations of abstract syntax trees with binders.
Coq's terms are represented in Elpi using the HOAS (Higher Order Abstract Syntax)
approach, i.e. the binders of lambda-prolog are used to represent the binders of Coq.

## Example
The Coq term `fun x : nat => S x` is represented as `lam "x" {{nat}} x\ app [ {{S}}, x ]`.
Note that `"x"` is just a name hint, and `{{nat}}` is a convenient quotation to
ask Coq to resolve `nat` into the corresponding global constant, internally represented
as something like `(indt "Coq.Init.Datatypes.nat")`. What is relevant is that `x\` is the
binding construct of lambda-prolog, and the `x` to which `{{S}}` is applied is bound.
As a consequence the following program fires a beta redex:
```
red (lam _ _ F) Arg Reduct :- Reduct = (F Arg).
red X _ X.
```
And the query `red (lam "x" {{nat}} x\ app [ {{S}}, x ]) {{0}} Result`
sets `Result` to `app [ {{S}}, {{0}} ]` as expected.

