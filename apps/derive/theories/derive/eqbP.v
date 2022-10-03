From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype.
Require Import eqb_core_defs.
Require Export tag fields eqb eqbcorrect derive.

From elpi.apps.derive Extra Dependency "eqbP.elpi" as eqbP.

Elpi Command derive.eqbP.
Elpi Accumulate Db derive.eqbcorrect.db.
Elpi Accumulate Db derive.eqb.db.
Elpi Accumulate File eqbP.
Elpi Accumulate lp:{{
 main [str I, str O] :- !, 
    coq.locate I (indt GR), 
    Prefix is O ^ "_",
    derive.eqbP.main GR Prefix _.

  main [str I] :- !, 
    coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.eqbP.main GR Prefix _.

  main _ :- usage.
   
  usage :- coq.error "Usage: derive.eqb <inductive name> [<prefix>]".

}}.
Elpi Typecheck.

Elpi Accumulate derive lp:{{

dep1 "eqbP" "eqbcorrect".
derivation T Prefix (derive "eqbP" (derive.eqbP.main T Prefix)).

}}.
Elpi Accumulate derive File eqbP.
