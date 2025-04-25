(* Generates the final, correctness lemma, for equality tests by combinig the
   output of eqcorrect and param1_inhab.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
From elpi.apps.derive.elpi Extra Dependency "paramX_lib.elpi" as paramX.
From elpi.apps.derive.elpi Extra Dependency "param1.elpi" as param1.
From elpi.apps.derive.elpi Extra Dependency "eqOK.elpi" as eqOK.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

From elpi Require Import elpi.
From elpi.apps Require Import derive.
From elpi.apps Require Import derive.param1 derive.param1_congr derive.param1_trivial derive.eqK derive.eqcorrect.

Elpi Db derive.eqOK.db lp:{{
  pred eqOK-done i:inductive.
}}.


(* standalone *)
Elpi Command derive.eqOK.
Elpi Accumulate File derive_hook.
Elpi Accumulate File paramX.
Elpi Accumulate Db Header derive.param1.db.
Elpi Accumulate File param1.
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1.trivial.db.
Elpi Accumulate Db derive.eqcorrect.db.
Elpi Accumulate Db derive.eqOK.db.

Elpi Accumulate File eqOK.
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I (indt GR), derive.eqOK.main GR O _.
  main [str I] :- !,
    coq.locate I (indt GR), Name is {coq.gref->id (indt GR)} ^ "_eq_OK",
    derive.eqOK.main GR Name _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.eqOK <inductive name> [<output name>]".
}}.  


  
(* hook into derive *)
Elpi Accumulate derive File eqOK.
Elpi Accumulate derive Db derive.eqOK.db.

#[phases="both"] Elpi Accumulate derive lp:{{
dep1 "eqOK" "eqcorrect".
dep1 "eqOK" "param1_trivial".
}}.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "eqOK" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{

derivation (indt T) Prefix ff (derive "eqOK" (derive.eqOK.main T N) (eqOK-done T)) :- N is Prefix ^ "eq_OK".

}}.
