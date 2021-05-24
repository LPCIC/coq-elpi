From elpi.apps Require Import eltac.cycle.

Goal True /\ False /\ 1=1.
split;[|split].
all: eltac.cycle 1.
admit.
reflexivity.
exact I.
Abort.

Goal True /\ False /\ 1=1.
split;[|split].
all: eltac.cycle -1.
reflexivity.
exact I.
admit.
Abort.

Goal True /\ False /\ 1=1.
split;[|split].
Fail all: eltac.cycle 3.
Abort.