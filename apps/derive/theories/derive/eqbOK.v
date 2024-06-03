(* Generates soudness proofs given correctness and reflexivity.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
   
Require Import eqb_core_defs.
Require Import tag eqType_ast fields eqb eqbcorrect derive.

From elpi.apps.derive.elpi Extra Dependency "eqbOK.elpi" as eqbOK.
From elpi.apps.derive.elpi Extra Dependency "eqType.elpi" as eqType.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

Elpi Db derive.eqbOK.db lp:{{

  pred eqbok-for o:gref, o:constant.

}}.

(* standalone *)
Elpi Command derive.eqbOK.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db derive.eqb.db.
Elpi Accumulate Db derive.eqbcorrect.db.
Elpi Accumulate Db derive.eqType.db.
Elpi Accumulate Db derive.eqbOK.db.
Elpi Accumulate File eqbOK.
Elpi Accumulate File eqType.
Elpi Accumulate lp:{{
  main [str I] :- !, 
    coq.locate I GR,
    coq.gref->id GR Tname,
    Prefix is Tname ^ "_",
    derive.eqbOK.main GR Prefix _.

  main _ :- usage.

  usage :- coq.error "Usage: derive.eqbOK <inductive name/alias>".

}}.
Elpi Typecheck.

(* hook into derive  *)
Elpi Accumulate derive File eqbOK.
Elpi Accumulate derive Db derive.eqbOK.db.

#[phases=both] Elpi Accumulate derive lp:{{
dep1 "eqbOK" "eqbcorrect".
dep1 "eqbOK-alias" "eqbcorrect-alias".
}}.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "eqbOK" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{

derivation (indt T) Prefix ff (derive "eqbOK" (derive.eqbOK.main (indt T) Prefix) (eqbok-for (indt T) _)).
derivation (const T) Prefix ff (derive "eqbOK-alias" (derive.eqbOK.main (const T) Prefix) (eqbok-for (const T) _)).

}}.
