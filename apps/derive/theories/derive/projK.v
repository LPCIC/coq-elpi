(* Generates a projection for each argument of each constructor.

   The projection is expected to be applied to an explicit construcor and all
   its arguments. It is used to implement "injection".

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Export elpi.

Elpi Db derive.projK.db lp:{{

type projK-db constructor -> int -> term -> prop.

:name "projK-db:fail"
projK-db GR N _ :-
  M is "derive.projK: can't find the projection " ^ {std.any->string N} ^ " for constructor " ^ {std.any->string GR},
  stop M.

}}.

Elpi Command derive.projK.
Elpi Accumulate Db derive.projK.db.
Elpi Accumulate File "elpi/projK.elpi".
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I (indt GR), derive.projK.main GR O _.
  main [str I] :- !, coq.locate I (indt GR), derive.projK.main GR "proj" _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.projK <inductive type name> [<output prefix>]".
}}.
Elpi Typecheck.
