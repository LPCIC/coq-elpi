(* For each constructor K the function isK returns true iff it is applied
   to K. These helpers are use to implement "discriminate".

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Export elpi.

(* Links the @gref of the constructor K to the isK constant *)
Elpi Db derive.isK.db lp:{{
  type isK-db constructor -> term -> prop.

  :name "isK-db:fail"
  isK-db K _ :-
    M is "No isK entry for constructor " ^ {std.any->string K} ^ ". Did you run derive.isK?",
    stop M.

}}.

Elpi Command derive.isK.
Elpi Accumulate Db derive.isK.db.
Elpi Accumulate File "elpi/isK.elpi".
Elpi Accumulate lp:{{
  main [str I,str O] :- !, coq.locate I (indt GR), derive.isK.main GR O _.
  main [str I] :- !,
    coq.locate I (indt GR),
    Prefix is {coq.gref->id (indt GR)} ^ "_is_",
    derive.isK.main GR Prefix _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.isK <inductive type name> [<output prefix>]".
}}.
Elpi Typecheck.
