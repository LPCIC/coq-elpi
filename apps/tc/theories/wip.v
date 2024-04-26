(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* --------------------------------------------------------------------------*)

Declare ML Module "coq-elpi-tc.plugin".
From elpi Require Import elpi.

From elpi.apps.tc Extra Dependency "base.elpi" as base.
From elpi.apps.tc Extra Dependency "modes.elpi" as modes.
From elpi.apps.tc Extra Dependency "ho_precompile.elpi" as ho_precompile.
From elpi.apps.tc Extra Dependency "ho_compile.elpi" as ho_compile.
From elpi.apps.tc Extra Dependency "compiler1.elpi" as compiler1.
From elpi.apps.tc Extra Dependency "ho_unif.elpi" as ho_unif.
From elpi.apps.tc Extra Dependency "parser_addInstances.elpi" as parser_addInstances.
From elpi.apps.tc Extra Dependency "alias.elpi" as alias.
From elpi.apps.tc Extra Dependency "solver.elpi" as solver.
From elpi.apps.tc Extra Dependency "rewrite_forward.elpi" as rforward.
From elpi.apps.tc Extra Dependency "tc_aux.elpi" as tc_aux.
From elpi.apps.tc Extra Dependency "create_tc_predicate.elpi" as create_tc_predicate.

From elpi.apps Require Import tc.
Set Warnings "+elpi".

Elpi Command AddForwardRewriting.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File ho_unif.
Elpi Accumulate File modes.
Elpi Accumulate File ho_precompile.
Elpi Accumulate File compiler1.
Elpi Accumulate File ho_compile.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate File solver.
Elpi Accumulate File rforward.
Elpi Accumulate lp:{{
  :before "build-hypotheses"
  build-hypotheses Ctx Clauses :- !,
    std.append Ctx {section-var->decl} CtxAndSection,
    tc.compile.instance.context {rewrite-dep CtxAndSection} Clauses. 

  main L :- 
    std.forall {args->str-list L} add-lemma->forward.
}}.
Elpi Typecheck.

Elpi Command AddAlias.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File ho_unif.
Elpi Accumulate File alias.
Elpi Accumulate lp:{{
  main [trm New, trm Old] :-
    add-tc-db _ _ (alias New Old).
}}.
Elpi Typecheck.