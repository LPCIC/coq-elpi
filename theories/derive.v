(* Generates a module containing all the derived constants.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Export
  derive.eq
  derive.isK
  derive.map
  derive.projK
  derive.param1
  derive.param1P
  derive.invert
  derive.induction
  derive.constsimplifier
.

Elpi Command derive.

Elpi Accumulate Db derive.eq.db.
Elpi Accumulate File "derive/eq.elpi".

Elpi Accumulate Db derive.isK.db.
Elpi Accumulate File "derive/isK.elpi".

Elpi Accumulate Db derive.map.db.
Elpi Accumulate File "derive/map.elpi".

Elpi Accumulate Db derive.projK.db.
Elpi Accumulate File "derive/projK.elpi".

Elpi Accumulate File "coq-lib-extra.elpi".

Elpi Accumulate Db derive.param1.db.
Elpi Accumulate File "derive/param1.elpi".

Elpi Accumulate Db derive.param1P.db.
Elpi Accumulate File "derive/param1P.elpi".

Elpi Accumulate Db derive.invert.db.
Elpi Accumulate File "derive/invert.elpi".

Elpi Accumulate Db derive.induction.db.
Elpi Accumulate File "derive/induction.elpi".

Elpi Accumulate File "derive/constsimplifier.elpi".

Elpi Accumulate File "derive/derive.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, derive.main I O.
  main [str I] :- !, derive.main I I.
  main _ :- usage.

  usage :-
    coq.error ""Usage: derive <inductive type name> [<output module name>]"".
".
Elpi Typecheck.
