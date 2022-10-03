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

Elpi Db derive.eqb.db lp:{{

  pred eqb-for
    o:term, % type1
    o:term, % type2
    o:term. % comparison function
  
  pred eqb-fields
    o:term, % type1
    o:term, % type2
    o:term. % eq_fields_type
  
  eqb-for {{ PrimFloat.float }} {{ PrimFloat.float }} {{ PrimFloat.eqb }}.
  eqb-for {{ PrimInt63.int }} {{ PrimInt63.int }} {{ PrimInt63.eqb }}.
  % eqb-for {{ @is_true lp:X }} {{ fun (_ _ : @is_true lp:X) => true }}.
  % eqb-for {{ @eq bool lp:X true }} {{ fun (_ _ : @eq bool lp:X true) => true }}.
     /* Generalize over bool and true, have a list of uip, i.e use  eqcorrect-for */ 
  eqb-for T1 T2 X :- whd1 T1 T1', !, eqb-for T1' T2 X. 
  eqb-for T1 T2 X :- whd1 T2 T2', !, eqb-for T1 T2' X. 
  
}}.

(* standalone *)
Elpi Command derive.fields.
Elpi Accumulate File derive_hook.
Elpi Accumulate File fields.
Elpi Accumulate File eqType.
Elpi Accumulate Db derive.eqType.db.
Elpi Accumulate Db derive.tag.db.
Elpi Accumulate Db derive.fields.db.
Elpi Accumulate Db derive.eqb.db.
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
Elpi Accumulate derive Db derive.eqb.db.
Elpi Accumulate derive Db derive.fields.db.
Elpi Accumulate derive lp:{{
  
dep1 "fields" "tag".
dep1 "fields" "eqType_ast".
derivation T Prefix (derive "fields" (derive.fields.main T Prefix)).

}}.
