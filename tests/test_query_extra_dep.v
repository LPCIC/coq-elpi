From elpi Require Import elpi.

From unreleased Extra Dependency "elpi_elaborator.elpi" as elab.

Elpi Command test.

Elpi Query lp:{{ coq.extra-dep "elab" (some P) }}.

Elpi Query lp:{{ coq.extra-dep "foo" none }}.
