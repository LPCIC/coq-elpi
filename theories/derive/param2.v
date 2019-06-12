(* Binary parametricity translation.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

Require Export elpi.

(* To be removed *)
Class param_db {X X1 XR : Type} (x : X) (x : X1) (xR : XR) := store_param {}.
Class param {X : Type} {XR : X -> X -> Type} (x : X) (xR : XR x x) := Param {}.

Elpi Command derive.param2.
Elpi Accumulate File "coq-lib-extra.elpi".
Elpi Accumulate File "derive/param2.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, coq.locate I GR, derive-param2 (global GR) O.
  main [str I] :- !,
    coq.locate I GR, coq.gr->id GR Id, O is Id ^ ""_param2"",
    derive-param2 (global GR) O.
  main _ :- usage.

  usage :- coq.error ""Usage: derive.param2 <object name> [<output name>]"".
". 
Elpi Typecheck.

