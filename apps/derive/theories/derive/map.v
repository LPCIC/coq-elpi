(* A map over a container. For non containers it produces the copy function.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
From elpi.apps.derive Extra Dependency "map.elpi" as map.
From elpi.apps.derive Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

From elpi Require Import elpi.
From elpi.apps Require Import derive.

(* Links the source and target type with the corresponding map function,
   eg. "map-db (list A) (list B) (list_map f_A_B)"
*)
Elpi Db derive.map.db lp:{{
  pred map-done i:inductive.
  pred map-db i:term, i:term, o:term.
}}.

(* standalone command *)
Elpi Command derive.map.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db derive.map.db.
Elpi Accumulate File map.
Elpi Accumulate lp:{{ 
  main [str I] :- !,
    coq.locate I (indt GR), O is {coq.gref->id (indt GR)} ^ "_",
    derive.map.main GR O _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.map <inductive type name>".
}}.
Elpi Typecheck.

(* hook into derive *)
Elpi Accumulate derive Db derive.map.db.
Elpi Accumulate derive File map.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "map" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{
  derivation (indt T) N ff (derive "map" (derive.map.main T N) (map-done T)).
}}.
