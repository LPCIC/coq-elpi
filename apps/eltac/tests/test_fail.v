From elpi.apps Require Import eltac.fail.

Goal False.
try (eltac.fail 0).
Fail try (eltac.fail 1).
Abort.
