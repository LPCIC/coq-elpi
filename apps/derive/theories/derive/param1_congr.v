(* Given an inductive type I and its unary parametricity translation is_I it
   generates for is constructor is_K a lemma like
      px = qx -> is_K x px .. = is_K x qx ..
   where px is the extra argument (about x) introduces by the parametricity
   translation.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
From elpi.apps.derive.elpi Extra Dependency "paramX_lib.elpi" as paramX.
From elpi.apps.derive.elpi Extra Dependency "param1_congr.elpi" as param1_congr.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

From elpi Require Export elpi.
From elpi.apps Require Export  derive.param1.

Elpi Db derive.param1.congr.db lp:{{
  type param1-congr-db constructor -> term -> prop. 
  type param1-congr-done gref -> prop. 
}}.

Elpi Command derive.param1.congr.
Elpi Accumulate File paramX.
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1.congr.db.
Elpi Accumulate File param1_congr.
Elpi Accumulate lp:{{
  main [str I, str O] :- !,
    coq.locate I (indt IsGR),
    realiR T {coq.env.global (indt IsGR)},
    coq.env.global (indt GR) T,
    derive.param1.congr.main (indt GR) (indt IsGR) O _.
  main [str I] :- !,
    coq.locate I (indt IsGR),
    realiR T {coq.env.global (indt IsGR)},
    coq.env.global (indt GR) T,
    derive.param1.congr.main (indt GR) (indt IsGR) "congr_" _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.param1.congr <inductive type name> [<output prefix>]".
}}.


(* hook into derive *)
Elpi Accumulate derive File param1_congr.
Elpi Accumulate derive Db derive.param1.congr.db.

#[phases="both"] Elpi Accumulate derive lp:{{
dep1 "param1_congr" "param1".
}}.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "param1_congr" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{

derivation T _ ff (derive "param1_congr" (derive.on_param1 T derive.param1.congr.main "congr_") (derive.on_param1 T (_\T\_\_\param1-congr-done T) _ _)).

}}.
