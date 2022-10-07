(* Generates the induction principle.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
From elpi.apps.derive Extra Dependency "paramX_lib.elpi" as paramX.
From elpi.apps.derive Extra Dependency "param1.elpi" as param1.
From elpi.apps.derive Extra Dependency "induction.elpi" as induction.
From elpi.apps.derive Extra Dependency "derive_hook.elpi" as derive_hook.

From elpi Require Import elpi.
From elpi.apps Require Import derive derive.param1 derive.param1_functor.

Elpi Db derive.induction.db lp:{{

type induction-db inductive -> term -> prop.

:name "induction-db:fail"
induction-db T _ :-
  M is "derive.induction: can't find the induction principle for " ^ {std.any->string T},
  stop M.

}}.

(* standalone *)
Elpi Command derive.induction.
Elpi Accumulate File derive_hook.
Elpi Accumulate File paramX.
Elpi Accumulate File param1.
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1.functor.db.
Elpi Accumulate Db derive.induction.db.
Elpi Accumulate File induction.
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I (indt GR), derive.induction.main GR O _.
  main [str I] :- !,
    coq.locate I (indt GR), Name is {coq.gref->id (indt GR)} ^ "_induction",
    derive.induction.main GR Name _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.induction <inductive type name> [<output name>]".
}}.  
Elpi Typecheck.

(* hook into derive *)
Elpi Accumulate derive File induction.
Elpi Accumulate derive Db derive.induction.db.
Elpi Accumulate derive lp:{{

dep1 "induction" "param1_functor".
derivation (indt T) Prefix (derive "induction" (derive.induction.main T N)) :- N is Prefix ^ "induction".

}}.
