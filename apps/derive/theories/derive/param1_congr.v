(* Given an inductive type I and its unary parametricity translation is_I it
   generates for is constructor is_K a lemma like
      px = qx -> is_K x px .. = is_K x qx ..
   where px is the extra argument (about x) introduces by the parametricity
   translation.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Export elpi. From elpi.apps Require Export  derive.param1.

Elpi Db derive.param1.congr.db lp:{{
  type param1-congr-db constructor -> term -> prop. 
}}.

Elpi Command derive.param1.congr.
Elpi Accumulate File "coq-lib-extra.elpi".
Elpi Accumulate Db derive.param1.congr.db.
Elpi Accumulate File "elpi/param1_congr.elpi".
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I (indt GR), derive.param1.congr.main GR O _.
  main [str I] :- !, coq.locate I (indt GR), derive.param1.congr.main GR "congr_" _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.param1.congr <inductive type name> [<output prefix>]".
}}.
Elpi Typecheck.
