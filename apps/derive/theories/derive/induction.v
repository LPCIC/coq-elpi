(* Generates the induction principle.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
From elpi.apps.derive.elpi Extra Dependency "paramX_lib.elpi" as paramX.
From elpi.apps.derive.elpi Extra Dependency "param1.elpi" as param1.
From elpi.apps.derive.elpi Extra Dependency "induction.elpi" as induction.
From elpi.apps.derive.elpi Extra Dependency "induction.db.elpi" as inductiondb.
From elpi.apps.derive.elpi Extra Dependency "param1.db.elpi" as param1db.
From elpi.apps.derive.elpi Extra Dependency "param1_functor.db.elpi" as param1_functordb.

From elpi Require Import elpi.
From elpi.apps Require Import derive derive.param1 derive.param1_functor.

Elpi Db derive.induction.db lp:{{ accumulate "elpi.apps.derive.elpi/induction.db". }}.

(* standalone *)
Elpi Command derive.induction.
Elpi Accumulate File param1.
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1.functor.db.
Elpi Accumulate Db derive.induction.db.
Elpi Accumulate File induction.
Elpi Accumulate lp:{{
  main [str I] :- !,
    coq.locate I (indt GR), Name is {coq.gref->id (indt GR)} ^ "_",
    derive.induction.main GR Name _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.induction <inductive type name>".
}}.  


(* hook into derive *)
Elpi Accumulate derive Db derive.induction.db.
Elpi Accumulate derive File induction.

#[phases="both"] Elpi Accumulate derive lp:{{
dep1 "induction" "param1_functor".
}}.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "induction" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{

derivation (indt T) N ff (derive "induction" (derive.induction.main T N) (induction-db T _)).

}}.
