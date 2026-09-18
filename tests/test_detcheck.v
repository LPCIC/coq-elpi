From elpi Require Import elpi.

Elpi Command test.
Elpi Db foo lp:{{/*(*/
  pred test -> pstring.
/*)*/}}.
Elpi File buggy_inline lp:{{/*(*/
data f A.
data s.
typeabbrev pstring (f s).
/*)*/}}.
Fail Elpi Accumulate foo File buggy_inline.
(* Elpi Accumulate Db foo.
Elpi Query lp:{{/*(*/
  coq.string->pstring "x" Primx,
  X = test Primx,
  coq.elpi.accumulate _ "foo" (clause _ _ X).
/*)*/}}. *)
