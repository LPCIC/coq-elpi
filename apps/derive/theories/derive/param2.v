(* Binary parametricity translation.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
From elpi.apps.derive Extra Dependency "paramX_lib.elpi" as paramX.
From elpi.apps.derive Extra Dependency "param2.elpi" as param2.

From elpi Require Export elpi.

(* To be removed *)
Class param_db {X X1 XR : Type} (x : X) (x : X1) (xR : XR) := store_param {}.
Class param {X : Type} {XR : X -> X -> Type} (x : X) (xR : XR x x) := Param {}.

Register store_param as param2.store_param.

(* Links a term (constant, inductive type, inductive constructor) with
   its parametricity translation *)
Elpi Db derive.param2.db lp:{{

    :index(3)
    pred param i:term, o:term, o:term.
    
    :name "param:fail"
    param X _ _ :-
      M is "derive.param2: No binary parametricity translation for " ^
              {coq.term->string X},
      stop M.
    
    type paramR term -> term -> term -> prop.
    
    :name "paramR:fail"
    paramR T T1 TR :-
      M is "derive.param2: No binary parametricity translation linking " ^
              {coq.term->string T} ^ " and " ^ {coq.term->string T1} ^ " and " ^ {coq.term->string TR},
      stop M.
    }}.
    

Elpi Command derive.param2.
Elpi Accumulate File paramX.
Elpi Accumulate File param2.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I GR, derive.param2.main GR O _.
  main [str I] :- !, coq.locate I GR, derive.param2.main GR "_R" _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.param2 <object name> [<output suffix>]".
}}. 
Elpi Typecheck.

