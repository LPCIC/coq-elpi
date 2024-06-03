(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* --------------------------------------------------------------------------*)

Declare ML Module "coq-elpi.tc".
From elpi Require Import elpi.

From elpi.apps.tc.elpi Extra Dependency "base.elpi" as base.
From elpi.apps.tc.elpi Extra Dependency "compiler.elpi" as compiler.
From elpi.apps.tc.elpi Extra Dependency "parser_addInstances.elpi" as parser_addInstances.
From elpi.apps.tc.elpi Extra Dependency "alias.elpi" as alias.
From elpi.apps.tc.elpi Extra Dependency "solver.elpi" as solver.
From elpi.apps.tc.elpi Extra Dependency "rewrite_forward.elpi" as rforward.
From elpi.apps.tc.elpi Extra Dependency "tc_aux.elpi" as tc_aux.
From elpi.apps.tc.elpi Extra Dependency "create_tc_predicate.elpi" as create_tc_predicate.

From elpi.apps Require Import tc.

Elpi Command AddForwardRewriting.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File compiler.
Elpi Accumulate File create_tc_predicate.
Elpi Accumulate File solver.
Elpi Accumulate File tc_aux.
Elpi Accumulate File rforward.
Elpi Accumulate lp:{{
  :before "build-context-clauses"
  build-context-clauses Ctx Clauses :- !,
    std.map {coq.env.section} 
      (x\r\ sigma F\ coq.env.typeof (const x) F, 
            r = (decl (global (const x)) _ F)) SectionCtx,
    std.append Ctx SectionCtx CtxAndSection,
    compile-ctx {rewrite-dep CtxAndSection} Clauses. 

  main L :- 
    std.forall {args->str-list L} add-lemma->forward.
}}.
Elpi Typecheck.

Elpi Command AddAlias.
Elpi Accumulate Db tc.db.
Elpi Accumulate Db tc_options.db.
Elpi Accumulate File base.
Elpi Accumulate File tc_aux.
Elpi Accumulate File alias.
Elpi Accumulate lp:{{
  main [trm New, trm Old] :-
    add-tc-db _ _ (alias New Old).
}}.
Elpi Typecheck.