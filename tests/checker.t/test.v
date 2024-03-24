From elpi Require Import elpi.

Elpi Command foo.
Elpi Accumulate lp:{{
pred p i:int.
p 0 0.

}}.
Fail Elpi Typecheck.

Elpi Command bar.
Elpi Accumulate lp:{{
pred p i:int.
p 0.

}}.
Elpi Typecheck.

Fail Elpi Typecheck foo.
