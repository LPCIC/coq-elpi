(* Binary parametricity translation.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Export elpi.

(* To be removed *)
Class param_db {X X1 XR : Type} (x : X) (x : X1) (xR : XR) := store_param {}.
Class param {X : Type} {XR : X -> X -> Type} (x : X) (xR : XR x x) := Param {}.

(* Links a term (constant, inductive type, inductive constructor) with
   its parametricity translation *)
Elpi Db derive.param2.db lp:{{

    :index(3)
    pred param i:term, o:term, o:term.
    
    :name "param:fail"
    param X _ _ :-
      coq.say "derive.param2: No binary parametricity translation for "
              {coq.term->string X},
      stop.
    
    type paramR term -> term -> term -> prop.
    
    :name "paramR:fail"
    paramR T T1 TR :-
      coq.say "derive.param2: No binary parametricity translation linking "
              {coq.term->string T} "and" {coq.term->string T1} "and" {coq.term->string TR},
      stop.
    }}.
    

Elpi Command derive.param2.
Elpi Accumulate File "coq-lib-extra.elpi".
Elpi Accumulate File "derive/param2.elpi".
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I GR, derive.param2.main GR O _.
  main [str I] :- !, coq.locate I GR, derive.param2.main GR "_R" _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.param2 <object name> [<output suffix>]".
}}. 
Elpi Typecheck.

