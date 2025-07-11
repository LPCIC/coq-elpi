From elpi.apps Require Import rbuild.

Record foo := { a : nat; b : bool }.

Check « false ; a := 3 » : foo.
