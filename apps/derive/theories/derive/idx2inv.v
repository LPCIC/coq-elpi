(* Generates lemmas linking an inductive with indexes and its structural
   copy without indexes but equations instead.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
From elpi.apps.derive.elpi Extra Dependency "paramX_lib.elpi" as paramX.
From elpi.apps.derive.elpi Extra Dependency "param1_functor.elpi" as param1_functor.
From elpi.apps.derive.elpi Extra Dependency "idx2inv.elpi" as idx2inv.
From elpi.apps.derive.elpi Extra Dependency "idx2inv.db.elpi" as idx2invdb.
From elpi.apps.derive.elpi Extra Dependency "invert.db.elpi" as invertdb.
From elpi.apps.derive.elpi Extra Dependency "param1.db.elpi" as param1db.
From elpi.apps.derive.elpi Extra Dependency "param1_functor.db.elpi" as param1_functordb.

From elpi Require Export elpi.
From elpi.apps Require Export derive.
From elpi.apps Require Export derive.param1 derive.param1_functor derive.invert.

Elpi Db derive.idx2inv.db lp:{{ accumulate "elpi.apps.derive.elpi/idx2inv.db". }}.

(* standalone *)
Elpi Command derive.idx2inv.
Elpi Accumulate File paramX.
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1.functor.db.
Elpi Accumulate File param1_functor.
Elpi Accumulate Db derive.invert.db.
Elpi Accumulate Db derive.idx2inv.db.
Elpi Accumulate File idx2inv.
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I (indt GR), derive.idx2inv.main GR O _.
  main [str I] :- !, coq.locate I (indt GR), derive.idx2inv.main GR "_to_" _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.idx2inv <inductive type name> [<separator>]".
}}.


(* hook into derive *)
Elpi Accumulate derive Db derive.idx2inv.db.
Elpi Accumulate derive File idx2inv.

#[phases="both"] Elpi Accumulate derive lp:{{
dep1 "idx2inv" "invert".
}}.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "idx2inv" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{

derivation (indt T) _ ff (derive "idx2inv" (derive.idx2inv.main T "_to_") (idx2inv-db T _ _ _)).

}}.
