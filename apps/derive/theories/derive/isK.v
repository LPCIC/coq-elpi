(* For each constructor K the function isK returns true iff it is applied
   to K. These helpers are use to implement "discriminate".

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
From elpi.apps.derive.elpi Extra Dependency "isK.elpi" as isK.
From elpi.apps.derive.elpi Extra Dependency "isK.db.elpi" as isKdb.

From elpi Require Import elpi.
From elpi.apps Require Import derive.

(* Links the @gref of the constructor K to the isK constant *)
Elpi Db derive.isK.db lp:{{ accumulate "elpi.apps.derive.elpi/isK.db". }}.

Elpi Command derive.isK.
Elpi Accumulate Db derive.isK.db.
Elpi Accumulate File isK.
Elpi Accumulate lp:{{

  main [str I,str O] :- !, coq.locate I (indt GR), derive.isK.main GR O _.
  main [str I] :- !,
    coq.locate I (indt GR),
    Prefix is {coq.gref->id (indt GR)} ^ "_",
    derive.isK.main GR Prefix _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.isK <inductive type name> [<output prefix>]".
}}.


(* hook into derive *)
Elpi Accumulate derive Db derive.isK.db.
Elpi Accumulate derive File isK.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "isK" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{
  
derivation (indt T) Prefix ff (derive "isK" (derive.isK.main T Prefix) (derive.exists-indc T (K\ isK-db K _))).

}}.
