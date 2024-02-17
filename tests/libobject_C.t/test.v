From elpi.tests Require Import test_libobject_B.

Goal True.
  b.
Abort.

Import elpi.

Elpi Accumulate a.db lp:{{ 
  :before "init" a {{ 3 }}.
}}.

Goal True.
b.
Abort.
