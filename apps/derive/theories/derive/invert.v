(* Generates inversion lemmas by encoding indexes with equations and non
   uniform parameters.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
From elpi.apps.derive Extra Dependency "invert.elpi" as invert.
From elpi.apps.derive Extra Dependency "derive_hook.elpi" as derive_hook.

From elpi Require Export elpi.
From elpi.apps Require Export derive.

Elpi Db derive.invert.db lp:{{ type invert-db gref -> gref -> prop. }}.

Elpi Command derive.invert.
Elpi Accumulate Db derive.invert.db.
Elpi Accumulate File invert.
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I (indt GR), derive.invert.main GR O _.
  main [str I] :- !, coq.locate I (indt GR), derive.invert.main GR "_inv" _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.invert <inductive type name> [<output name>]".
}}.
Elpi Typecheck.

(* hook into derive *)
Elpi Accumulate derive File invert.
Elpi Accumulate derive Db derive.invert.db.
Elpi Accumulate derive lp:{{
  
derivation T Prefix (derive "invert" (derive.invert.main T N)) :- N is Prefix ^ "inv".

}}.
