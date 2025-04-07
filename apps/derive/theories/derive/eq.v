(* Generates equality tests.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
From elpi.apps.derive.elpi Extra Dependency "eq.elpi" as eq.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

From elpi Require Import elpi.
From elpi.apps Require Import derive.

From elpi.core Require Import PrimInt63 PrimFloat PrimString.

Register Coq.Numbers.Cyclic.Int63.PrimInt63.eqb as elpi.derive.eq_unit63.
Register Coq.Floats.PrimFloat.eqb as elpi.derive.eq_float64.

Elpi Db derive.eq.db lp:{{

% full resolution (composes with eq functions for parameters)
type eq-db term -> term -> term -> prop.
eq-db {{ lib:num.int63.type }} {{ lib:num.int63.type }} {{ lib:elpi.derive.eq_unit63 }} :- !.
eq-db {{ lib:num.float.type }} {{ lib:num.float.type }} {{ lib:elpi.derive.eq_float64 }} :- !.
eq-db {{ lib:elpi.pstring }} {{ lib:elpi.pstring }} {{ lib:elpi.pstring_eqb }} :- !.

% quick access
type eq-for inductive -> constant -> prop.

}}.
#[superglobal] Elpi Accumulate derive.eq.db lp:{{

pred whd1 i:term, o:term.

:name "eq-db:fail"
eq-db A B F :-
  ((whd1 A A1, B1 = B); (whd1 B B1, A1 = A)), !,
  eq-db A1 B1 F.

eq-db A B _ :-
  M is "derive.eq: can't find the comparison function for terms of type " ^
          {coq.term->string A} ^ " and " ^ {coq.term->string B} ^ " respectively",
  stop M.

}}.

Elpi Command derive.eq.
Elpi Accumulate File derive_hook.
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
