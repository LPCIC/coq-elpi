From elpi Require Import elpi.

Elpi Db tc.db lp:{{
  pred a i:int.
}}.

Elpi Command C.
Elpi Accumulate Db tc.db.

Section A.
  Elpi Query lp:{{
    @global! => coq.elpi.accumulate _ "tc.db" (clause _ _ (a 2)).
  }}.
  Elpi Print C "C.html" ".*elpi.[^a].*" ".*:.*[0-9]+".
End A.

Elpi Print C "C.html" ".*elpi.[^a].*" ".*:.*[0-9]+".  
