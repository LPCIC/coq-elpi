From elpi Require Import elpi.
From elpi.apps Require Import derive.
From Coq Require Import PArith.
From elpi.apps.derive Extra Dependency "tag.elpi" as tag.
From elpi.apps.derive Extra Dependency "derive_hook.elpi" as derive_hook.

Register positive as elpi.derive.positive.

Local Open Scope positive_scope.

Elpi Db derive.tag.db lp:{{

% this is how one registers the tag function to an inductive and let other
% elpi commands use that piece of info
pred tag-for o:inductive, o:constant.

}}.

(* standalone *)
Elpi Command derive.tag.
Elpi Accumulate File derive_hook.
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
Elpi Typecheck.

(* hook into derive *)
Elpi Accumulate derive Db derive.tag.db.
Elpi Accumulate derive File tag.
Elpi Accumulate derive lp:{{
  
derivation (indt T) Prefix (derive "tag" (derive.tag.main T Prefix) (tag-for T _)).

}}.
