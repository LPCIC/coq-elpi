From elpi Require Import elpi.
From elpi.apps Require Import derive.
From Corelib Require Import PosDef.
From elpi.apps.derive.elpi Extra Dependency "tag.elpi" as tag.
From elpi.apps.derive.elpi Extra Dependency "tag.db.elpi" as tagdb.

Register positive as elpi.derive.positive.

Local Open Scope positive_scope.

Elpi Db derive.tag.db lp:{{ accumulate "elpi.apps.derive.elpi/tag.db". }}.

(* standalone *)
Elpi Command derive.tag.
Elpi Accumulate File tag.
Elpi Accumulate Db derive.tag.db.
Elpi Accumulate lp:{{

  main [str I] :- !, 
    coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.tag.main GR Prefix _.

  main _ :- usage.
   
  usage :- coq.error "Usage: derive.tag <inductive name>".

}}.


(* hook into derive *)
Elpi Accumulate derive Db derive.tag.db.
Elpi Accumulate derive File tag.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "tag" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{
  
derivation (indt T) Prefix ff (derive "tag" (derive.tag.main T Prefix) (tag-for T _)).

}}.
