Require Import elpi.

(* To be removed *)
Class reali_db {X XR : Type} (x : X) (xR : XR) := store_reali {}.
Class reali {X : Type} {XR : X -> Type} (x : X) (xR : XR x) := Reali {}.

Elpi Db derive.param1.db " type param1-db term -> term -> prop. ".

Elpi Command derive.param1.
Elpi Accumulate File "coq-lib-extra.elpi".
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate File "derive/param1.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, derive-param1 I O.
  main [str I] :- !,
    coq-locate I T, term->gr T GR, coq-gr->id GR Id, O is Id ^ ""_param1"",
    derive-param1 I O.
  main _ :- usage.

  usage :- coq-error ""Usage: derive.param1 <object name> [<output name>]"".
". 
Elpi Typecheck.

