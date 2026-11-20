(* Binary parametricity translation.

   license: GNU Lesser General Public License Version 2.1 or later
   ------------------------------------------------------------------------- *)
From elpi.apps.derive.elpi Extra Dependency "paramX_lib.elpi" as paramX.
From elpi.apps.derive.elpi Extra Dependency "param2.elpi" as param2.
From elpi.apps.derive.elpi Extra Dependency "param1.db.elpi" as param1db.
From elpi.apps.derive.elpi Extra Dependency "param2.db.elpi" as param2db.

From elpi Require Import elpi.
From elpi.apps Require Import derive.

(* To be removed *)
Class param_db {X X1 XR : Type} (x : X) (x : X1) (xR : XR) := store_param {}.
Class param {X : Type} {XR : X -> X -> Type} (x : X) (xR : XR x x) := Param {}.

Register store_param as param2.store_param.

(* Links a term (constant, inductive type, inductive constructor, record type,
   projection) with its parametricity translation *)
Elpi Db derive.param2.db lp:{{ accumulate "elpi.apps.derive.elpi/param2.db". }}.
(* not in param2.db.elpi: these rules come after the ones of param2.elpi *)
#[superglobal] Elpi Accumulate derive.param2.db lp:{{

    % queries param.gref and lifts answer to terms.
    func dispatch-gref gref -> term,term.
    dispatch-gref GRT U TR :-
      param.gref GRT GRU GRR,
      coq.env.global GRU U,
      coq.env.global GRR TR.

    :name "param:gref"
    param T U TR :-
      coq.env.global GRT T,
      dispatch-gref GRT U TR, !.

    :name "paramR:gref"
    paramR T U TR :-
      coq.env.global GRT T,
      dispatch-gref GRT U TR, !.

    :name "param:fail"
    param X _ _ :-
      M is "derive.param2: No binary parametricity translation for " ^
              {coq.term->string X},
      stop M.

    :name "paramR:fail"
    paramR T T1 TR :-
      M is "derive.param2: No binary parametricity translation linking " ^
              {coq.term->string T} ^ " and " ^ {coq.term->string T1} ^ " and " ^ {coq.term->string TR},
      stop M.
}}.


Elpi Command derive.param2.
Elpi Accumulate File param2.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I GR, derive.param2.main GR "" _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.param2 <object name>".
}}.

Elpi Command derive.param2.register.
Elpi Accumulate File param2.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate lp:{{
  main [str I, str R] :- !, coq.locate I GRI, coq.locate R GRR,
    derive.param2.main_register GRI GRR.
  main _ :- usage.

  usage :- coq.error "Usage: derive.param2.register <name> <name_R>".
}}.


(* hook into derive *)
Elpi Accumulate derive File param2.
Elpi Accumulate derive Db derive.param2.db.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "param2" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{

derivation T N ff (derive "param2" (derive.param2.main T N) (param-done T)).

}}.
