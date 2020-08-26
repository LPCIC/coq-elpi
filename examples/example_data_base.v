From elpi Require Import elpi.

(** Data bases are accumulated by name, hence can be shared among multiple
    commands or across successive executions of the same command.
    
    Let's start with a db containing international phone prefixes *)

Elpi Db phonebook.db lp:{{ 
  pred phone_prefix o:string, o:int.
  phone_prefix "USA" 1.
}}.

Elpi Command print_db.
Elpi Accumulate Db phonebook.db.
Elpi Accumulate lp:{{
  main [] :- std.findall (phone_prefix S_ N_) L, !, coq.say "The Db contains" L.
  main [str S] :- coq.say "Phone prefix for" S "is" {phone_prefix S}, !.
  main [str S] :- coq.error "No prefix for" S.
}}.
Elpi Typecheck.

Elpi print_db.
Elpi print_db USA.
Fail Elpi print_db Italy.

Elpi Command add_db.
Elpi Accumulate Db phonebook.db.
Elpi Accumulate lp:{{
  main [str S, int N] :-
    coq.elpi.accumulate _ "phonebook.db" (clause _ _ (phone_prefix S N)).
}}.
Elpi Typecheck.

Elpi add_db France 33.
Elpi add_db Italy 39.
Elpi print_db.
Elpi print_db France.

(** Data bases don't need to be that simple, they can contain
    arbitrary clauses, in particular conditional ones. *)

Elpi Db food.db lp:{{

  pred sweet i:string.
  sweet "apricot".

  pred tasty i:string.
  tasty "salmon".

}}.
Elpi Command add_recipy.
Elpi Accumulate Db food.db.
Elpi Accumulate lp:{{
  pred test-sweetness i:argument, o:prop.
  test-sweetness (str X) (sweet X).

  pred test-tastiness i:argument, o:prop.
  test-tastiness (str X) (tasty X).

  main [str Name|Ingredients] :-
    std.map Ingredients test-sweetness SweetConditions,
    % trick: ":-" accepts a list of propositions on the RHS
    coq.elpi.accumulate _ "food.db" (clause _ _ (sweet Name :- SweetConditions)),

    std.map Ingredients test-tastiness TastyConditions,
    std.forall TastyConditions (i\
      coq.elpi.accumulate _ "food.db" (clause _ _ (tasty Name :- i))).
}}.
Elpi Typecheck.

Elpi Command is_sweet.
Elpi Accumulate Db food.db.
Elpi Accumulate lp:{{
  main [str Name] :- if (sweet Name) (coq.say "sweet!") (coq.say "brr").
}}.
Elpi Typecheck.

Elpi Command is_tasty.
Elpi Accumulate Db food.db.
Elpi Accumulate lp:{{
  main [str Name] :- if (tasty Name) (coq.say "yummy!") (coq.say "bohf").
}}.
Elpi Typecheck.

Elpi add_recipy "pie"   "potato" "salmon".
Elpi add_recipy "jam"   "apricot".
Elpi add_recipy "tart"  "jam".

Elpi is_sweet "tart".
Elpi is_sweet "pie".
Elpi is_tasty "pie".


