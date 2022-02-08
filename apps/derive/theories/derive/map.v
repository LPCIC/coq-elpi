(* A map over a container. For non containers it produces the copy function.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Export elpi.

(* Links the source and target type with the corresponding map function,
   eg. "map-db (list A) (list B) (list_map f_A_B)" *)
Elpi Db derive.map.db lp:{{ type map-db term -> term -> term -> prop. }}.

Elpi Command derive.map.
Elpi Accumulate Db derive.map.db.
Elpi Accumulate File "map.elpi" From elpi.apps.derive.
Elpi Accumulate lp:{{ 
  main [str I, str O] :- !, coq.locate I (indt GR), derive.map.main GR O _.
  main [str I] :- !,
    coq.locate I (indt GR), O is {coq.gref->id (indt GR)} ^ "_map",
    derive.map.main GR O _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.map <inductive type name> [<output name>]".
}}.
Elpi Typecheck.
