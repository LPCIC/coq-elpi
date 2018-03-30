Require Import elpi.

(* I'm not sure param1P is a reasonable name for this derivation *)

Elpi Db derive.param1P.db "type param1P-db term -> term -> prop.".

Elpi Command derive.param1P.
Elpi Accumulate Db derive.param1P.db.
Elpi Accumulate File "derive/param1P.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, derive.param1P.main I O _.
  main [str I] :- !, derive.param1P.main I ""P"" _.
  main _ :- usage.

  usage :- coq.error ""Usage: derive.param1P <inductive type name>"".
". 
Elpi Typecheck.

