Require Export
  elpi.elpi.

Elpi Command C.
Fail Elpi Accumulate  lp:{{
  pred p.
  
  p :- copy X Y => true.


}}.
