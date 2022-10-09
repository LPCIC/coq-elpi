(* Generates lemmas linking an inductive with indexes and its structural
   copy without indexes but equations instead.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
From elpi.apps.derive Extra Dependency "paramX_lib.elpi" as paramX.
From elpi.apps.derive Extra Dependency "param1_functor.elpi" as param1_functor.
From elpi.apps.derive Extra Dependency "idx2inv.elpi" as idx2inv.
From elpi.apps.derive Extra Dependency "derive_hook.elpi" as derive_hook.

From elpi Require Export elpi.
From elpi.apps Require Export derive.
From elpi.apps Require Export derive.param1 derive.param1_functor derive.invert.

Elpi Db derive.idx2inv.db lp:{{
  type idx2inv-db inductive -> inductive -> constant -> constant -> prop.
}}.

(* standalone *)
Elpi Command derive.idx2inv.
Elpi Accumulate File derive_hook.
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
Elpi Typecheck.

(* hook into derive *)
Elpi Accumulate derive Db derive.idx2inv.db.
Elpi Accumulate derive File idx2inv.
Elpi Accumulate File paramX.
Elpi Accumulate derive lp:{{

dep1 "idx2inv" "invert".
derivation (indt T) _ (derive "idx2inv" (derive.idx2inv.main T "_to_") (idx2inv-db T _ _ _)).

}}.
