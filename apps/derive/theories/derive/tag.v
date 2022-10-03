From elpi Require Import elpi.
From Coq Require Import PArith.
From elpi.apps.derive Extra Dependency "tag.elpi" as tag.

Register positive as elpi.derive.positive.

Local Open Scope positive_scope.

Elpi Db derive.tag.db lp:{{

% this is how one registers the tag function to an inductive and let other
% elpi commands use that piece of info
pred tag-for o:inductive, o:constant.

}}.

Elpi Command derive.tag.
Elpi Accumulate File tag.
Elpi Accumulate Db derive.tag.db.
Elpi Accumulate lp:{{
  main [str I, str O] :- !, 
    coq.locate I (indt GR), 
    Prefix is O ^ "_",
    derive.tag.main GR Prefix _.

  main [str I] :- !, 
    coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.tag.main GR Prefix _.

  main _ :- usage.
   
  usage :- coq.error "Usage: derive.tag <inductive name> [<prefix>]".

}}.
Elpi Typecheck.
