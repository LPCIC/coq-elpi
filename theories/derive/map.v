(* A map over a container. For non containers it produces the copy function.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

Require Export elpi.

(* Links the source and target type with the corresponding map function,
   eg. "map-db (list A) (list B) (list_map f_A_B)" *)
Elpi Db derive.map.db lp:{{ type map-db term -> term -> term -> prop. }}.

Elpi Command derive.map.
Elpi Accumulate Db derive.map.db.
Elpi Accumulate File "derive/map.elpi".
Elpi Accumulate lp:{{ 
  main [str I, str O] :- !, coq.locate I GR, derive.map.main (global GR) O _.
  main [str I] :- !,
    coq.locate I GR, O is {coq.gr->id GR} ^ "_map",
    derive.map.main (global GR) O _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.map <inductive type name> [<output name>]".
}}.
Elpi Typecheck.
