(* Generates soudness proofs given correctness and reflexivity.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
   
Require Import eqb_core_defs.
Require Import tag eqType_ast fields eqb eqbcorrect derive.

From elpi.apps.derive Extra Dependency "eqbOK.elpi" as eqbOK.
From elpi.apps.derive Extra Dependency "eqType.elpi" as eqType.
From elpi.apps.derive Extra Dependency "derive_hook.elpi" as derive_hook.

Elpi Db derive.eqbOK.db lp:{{

  pred eqbok-for o:inductive, o:constant.

}}.

(* standalone *)
Elpi Command derive.eqbOK.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db derive.eqbcorrect.db.
Elpi Accumulate Db derive.eqType.db.
Elpi Accumulate Db derive.eqbOK.db.
Elpi Accumulate File eqbOK.
Elpi Accumulate File eqType.
Elpi Accumulate lp:{{
 main [str I, str O] :- !, 
    coq.locate I (indt GR), 
    Prefix is O ^ "_",
    derive.eqbOK.main GR Prefix _.

  main [str I] :- !, 
    coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.eqbOK.main GR Prefix _.

  main _ :- usage.
   
  usage :- coq.error "Usage: derive.eqbOK <inductive name> [<prefix>]".

}}.
Elpi Typecheck.

(* hook into derive  *)
Elpi Accumulate derive File eqbOK.
Elpi Accumulate derive Db derive.eqbOK.db.
Elpi Accumulate derive lp:{{

dep1 "eqbOK" "eqbcorrect".
derivation (indt T) Prefix (derive "eqbOK" (derive.eqbOK.main T Prefix) (eqbok-for T _)).

}}.
