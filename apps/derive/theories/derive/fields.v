From elpi Require Import elpi.
From elpi.apps Require Import derive.
From Coq Require Import PArith.
From elpi.apps Require Export derive.eqType_ast derive.tag.
From elpi.apps.derive Extra Dependency "fields.elpi" as fields.
From elpi.apps.derive Extra Dependency "eqType.elpi" as eqType.
From elpi.apps.derive Extra Dependency "derive_hook.elpi" as derive_hook.

Register unit as elpi.derive.unit.

Local Open Scope positive_scope.

Elpi Db derive.fields.db lp:{{

% this is how one registers the fields_t, fields and construct[P]
% constants to an inductive and let other elpi commands use that piece of info
pred fields-for
  o:inductive,
  o:constant, % fields_t
  o:constant, % fields
  o:constant, % construct
  o:constant. % constructP

pred box-for o:constructor, o:inductive, o:constructor.

}}.

(* standalone *)
Elpi Command derive.fields.
Elpi Accumulate File derive_hook.
Elpi Accumulate File fields.
Elpi Accumulate File eqType.
Elpi Accumulate Db derive.eqType.db.
Elpi Accumulate Db derive.tag.db.
Elpi Accumulate Db derive.fields.db.
Elpi Accumulate lp:{{
  main [str I, str O] :- !, 
    coq.locate I (indt GR), 
    Prefix is O ^ "_",
    derive.fields.main GR Prefix _.

  main [str I] :- !, 
    coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.fields.main GR Prefix _.

  main _ :- usage.
   
  usage :- coq.error "Usage: derive.fields <inductive name> [<prefix>]".

}}.
Elpi Typecheck.

(* hook into derive *)
Elpi Accumulate derive File fields.
Elpi Accumulate derive Db derive.fields.db.
Elpi Accumulate derive lp:{{
  
dep1 "fields" "tag".
dep1 "fields" "eqType_ast".
derivation (indt T) Prefix (derive "fields" (derive.fields.main T Prefix)).

}}.
