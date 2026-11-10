From elpi Require Import elpi.
From elpi.apps Require Import derive.
From Corelib Require Import PosDef.
From elpi.apps Require Export derive.eqType_ast derive.tag.
From elpi.apps.derive.elpi Extra Dependency "fields.elpi" as fields.
From elpi.apps.derive.elpi Extra Dependency "eqType.elpi" as eqType.
From elpi.apps.derive.elpi Extra Dependency "eqType.db.elpi" as eqTypedb.
From elpi.apps.derive.elpi Extra Dependency "fields.db.elpi" as fieldsdb.
From elpi.apps.derive.elpi Extra Dependency "tag.db.elpi" as tagdb.

Register unit as elpi.derive.unit.

Local Open Scope positive_scope.

Elpi Db derive.fields.db lp:{{ accumulate "elpi.apps.derive.elpi/fields.db". }}.

(* standalone *)
Elpi Command derive.fields.
Elpi Accumulate File fields.
Elpi Accumulate Db derive.eqType.db.
Elpi Accumulate Db derive.tag.db.
Elpi Accumulate Db derive.fields.db.
Elpi Accumulate lp:{{

  main [str I] :- !, 
    coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.fields.main GR Prefix _.

  main _ :- usage.
   
  usage :- coq.error "Usage: derive.fields <inductive name> [<prefix>]".

}}.


(* hook into derive *)
Elpi Accumulate derive Db derive.fields.db.
Elpi Accumulate derive File fields.

#[phases="both"] Elpi Accumulate derive lp:{{
dep1 "fields" "tag".
dep1 "fields" "eqType_ast".
}}.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "fields" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{

derivation (indt T) Prefix ff (derive "fields" (derive.fields.main T Prefix) (fields-for T _ _ _ _)).

}}.
