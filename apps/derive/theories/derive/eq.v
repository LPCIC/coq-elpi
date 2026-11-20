(* Generates equality tests.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
From elpi.apps.derive.elpi Extra Dependency "eq.elpi" as eq.
From elpi.apps.derive.elpi Extra Dependency "eq.db.elpi" as eqdb.

From elpi Require Import elpi.
From elpi.apps Require Import derive.

From Corelib Require Import PrimInt63 PrimFloat.
From elpi.apps.derive Require Import PrimStringEqb.

Register Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb as elpi.derive.eq_unit63.
Register Corelib.Floats.PrimFloat.eqb as elpi.derive.eq_float64.

Elpi Db derive.eq.db lp:{{ accumulate "elpi.apps.derive.elpi/eq.db". }}.

Elpi Command derive.eq.
Elpi Accumulate Db derive.eq.db.
Elpi Accumulate File eq.
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I (indt GR), derive.eq.main GR O _.
  main [str I] :- !, 
    coq.locate I (indt GR), coq.gref->id (indt GR) Id, O is Id ^ "_eq",
    derive.eq.main GR O _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.eq <inductive type name> [<output name>]".
}}.


(* hook into derive *)
Elpi Accumulate derive Db derive.eq.db.
Elpi Accumulate derive File eq.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "eq" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{
  
derivation (indt T) Prefix ff (derive "eq" (derive.eq.main T N) (eq-for T _)) :- N is Prefix ^ "eq".

}}.
