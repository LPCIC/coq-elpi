From elpi Require Import elpi.
From elpi.apps Require Import derive derive.param1.
From Coq Require Import ssrbool ssreflect Uint63.
From Coq Require Import PArith.

From elpi.apps.derive Extra Dependency "fields.elpi" as fields.
From elpi.apps.derive Extra Dependency "eqb.elpi" as eqb.
From elpi.apps.derive Extra Dependency "eqType.elpi" as eqType.
From elpi.apps.derive Extra Dependency "derive_hook.elpi" as derive_hook.

Require Import eqb_core_defs.
Require Import eqType_ast tag fields.

Register eqb_body as elpi.derive.eqb_body.

Lemma uint63_eqb_correct i : eqb_correct_on PrimInt63.eqb i.
Proof. by move=> j; case: (Uint63.eqb_spec i j); case: PrimInt63.eqb. Qed.

Lemma uint63_eqb_refl i : eqb_refl_on PrimInt63.eqb i.
Proof. by case: (Uint63.eqb_spec i i) => _ H; exact: H. Qed.

Elpi Db derive.eqbcorrect.db lp:{{

  pred eqcorrect-for
    o:gref,
    o:constant, % correct
    o:constant. % reflexive
  
  eqcorrect-for {{:gref PrimInt63.int }} C R :-
    {{:gref uint63_eqb_correct}} = const C,
    {{:gref uint63_eqb_refl}} = const R.

  :index(2)
  pred correct-lemma-for i:term, o:term.
  correct-lemma-for {{ PrimInt63.int }} {{ @uint63_eqb_correct }}.

  :index(2)
  pred refl-lemma-for i:term, o:term.
  refl-lemma-for {{ PrimInt63.int }} {{ @uint63_eqb_refl }}.

}}.

(* standalone *)
Elpi Command derive.eqb.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db derive.tag.db.
Elpi Accumulate Db derive.eqType.db.
Elpi Accumulate Db derive.fields.db.
Elpi Accumulate Db derive.eqb.db.
Elpi Accumulate Db derive.eqbcorrect.db.
Elpi Accumulate File fields.
Elpi Accumulate File eqb.
Elpi Accumulate File eqType.

Elpi Accumulate lp:{{

  main [str I, str O] :- !, 
    coq.locate I (indt GR), 
    Prefix is O ^ "_",
    derive.eqb.main GR Prefix _.

  main [str I] :- !, 
    coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.eqb.main GR Prefix _.

  main _ :- usage.
   
  usage :- coq.error "Usage: derive.eqb <inductive name> [<prefix>]".

}}.
Elpi Typecheck.

(* hook into derive *)
Elpi Accumulate derive Db derive.eqb.db.
Elpi Accumulate derive File eqb.
Elpi Accumulate derive lp:{{

dep1 "eqb" "fields".
derivation (indt T) Prefix (derive "eqb" (derive.eqb.main T Prefix)).

}}.
