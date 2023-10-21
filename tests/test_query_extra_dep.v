From elpi Require Import elpi.

From unreleased Extra Dependency "elpi_elaborator.elpi" as elab.

Elpi Query lp:{{ coq.extra-dep "elab" _ }}.

Fail Elpi Query lp:{{ coq.extra-dep "foo" (some _) }}.
