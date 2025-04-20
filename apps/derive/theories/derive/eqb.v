From elpi Require Import elpi.
From elpi.apps Require Import derive derive.param1.
From elpi.core Require Import ssrbool ssreflect PrimInt63.
From elpi.core Require Import PosDef.

From elpi.apps.derive.elpi Extra Dependency "fields.elpi" as fields.
From elpi.apps.derive.elpi Extra Dependency "eqb.elpi" as eqb.
From elpi.apps.derive.elpi Extra Dependency "eqType.elpi" as eqType.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

Require Import eqb_core_defs.
Require Import eqType_ast tag fields.

Register eqb_body as elpi.derive.eqb_body.

Elpi Db derive.eqb.db lp:{{
  pred whd1 i:term, o:term.
  
  pred eqb-done o:gref.

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
  eqb-for {{ lib:elpi.pstring }} {{ lib:elpi.pstring }} {{ lib:elpi.pstring_eqb }}.

  :name "eqb-for:whd"
  eqb-for T1 T2 X :- whd1 T1 T1', !, eqb-for T1' T2 X. 
  eqb-for T1 T2 X :- whd1 T2 T2', !, eqb-for T1 T2' X. 
  
}}.

(* standalone *)
Elpi Command derive.eqb.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db derive.tag.db.
Elpi Accumulate Db derive.eqType.db.
Elpi Accumulate Db derive.fields.db.
Elpi Accumulate Db derive.eqb.db.
Elpi Accumulate File fields.
Elpi Accumulate File eqb.
Elpi Accumulate File eqType.

Elpi Accumulate lp:{{

  main [str I] :- !, 
    coq.locate I GR,
    coq.gref->id GR Tname,
    Prefix is Tname ^ "_",
    derive.eqb.main GR Prefix _.

  main _ :- usage.
   
  usage :- coq.error "Usage: derive.eqb <inductive name/alias definition>".

}}.


(* hook into derive *)
Elpi Accumulate derive Db derive.eqb.db.
Elpi Accumulate derive File eqb.

#[phases="both"] Elpi Accumulate derive lp:{{
dep1 "eqb" "fields".
}}.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "eqb" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{

derivation (indt T)  Prefix ff (derive "eqb" (derive.eqb.main (indt T) Prefix) (eqb-done (indt T))).
derivation (const C) Prefix ff (derive "eqb_alias" (derive.eqb.main (const C) Prefix) (eqb-done (const C))).

}}.
