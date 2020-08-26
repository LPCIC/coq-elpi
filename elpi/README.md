### coq-HOAS

Documents how Coq terms are represented in Elpi.

### coq-lib

Standard library of Coq specific utilities (in the coq. namespace).

### elpi-command-template

Selects which files are accumulated in an `Elpi Command`.

### elpi-tactic-template

Selects which files are accumulated in an `Elpi Tactic`.

### coq-elpi-checker

Extends the standard type checker for Elpi programs so that it reports
errors using Coq's I/O primitives.

### elpi-ltac

Implementation of Ltac's like combinators in Elpi.

### elpi-reduction

Implementation of reduction in Elpi. Main entry points are `whd` and `hd-beta`.

### coq-elaborator

Uses the Coq type inference and unification algorithms in order to implement
`of`, `unify-*` and `evar`.

### elpi-elaborator

An elaborator completely written in Elpi (work in progress). It implements
`of`, `unify-*` and `evar`.
