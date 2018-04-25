(* Given an inductive type I and its unary parametricity translation IR it
   generates a proof IP that "forall i : I, IR i".

   It is used for the derivation of induction principles.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

Require Import elpi.

Elpi Db derive.param1P.db "

type param1P-db term -> term -> prop.

% Plase holder to inject clauses with high priority
:name ""param1P:begin"" param1P-db _ _ :- fail.

".

Elpi Command derive.param1P.
Elpi Accumulate Db derive.param1P.db.
Elpi Accumulate File "derive/param1P.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, derive.param1P.main I O _.
  main [str I] :- !, derive.param1P.main I ""P"" _.
  main _ :- usage.

  usage :-
    coq.error ""Usage: derive.param1P <inductive type name> [<output suffix>]"".
". 
Elpi Typecheck.

