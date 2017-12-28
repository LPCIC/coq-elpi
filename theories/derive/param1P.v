Require Import elpi.

(* I'm not sure param1P is a reasonable name for this derivation *)

Elpi Db derive.param1P.db "type param1P-db term -> term -> prop.".

Elpi Command derive.param1P.
Elpi Accumulate Db derive.param1P.db.
Elpi Accumulate File "derive/param1P.elpi".
Elpi Accumulate "
  main [str I] :- !,
    coq-locate I (indt GR), coq-gr->id GR Id, O is Id ^ ""P"",
    derive-param1P GR O.
  main _ :- usage.

  usage :- coq-error ""Usage: derive.param1P <inductive type name>"".
". 
Elpi Typecheck.

