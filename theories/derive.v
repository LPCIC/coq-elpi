(* Generates a module containing all the derived constants.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Export
  derive.eq
  derive.isK
  derive.map
  derive.projK
  derive.param1
  derive.param1_congr
  derive.param1_inhab
  derive.param1_trivial
  derive.invert
  derive.idx2inv
  derive.induction
  derive.bcongr
  derive.eqK
  derive.eqcorrect
  derive.eqOK
  derive.param2
.

Elpi Command derive.

Elpi Accumulate Db derive.eq.db.
Elpi Accumulate File "derive/eq.elpi".

Elpi Accumulate Db derive.isK.db.
Elpi Accumulate File "derive/isK.elpi".

Elpi Accumulate Db derive.map.db.
Elpi Accumulate File "derive/map.elpi".

Elpi Accumulate Db derive.projK.db.
Elpi Accumulate File "derive/projK.elpi".

Elpi Accumulate File "coq-lib-extra.elpi".

Elpi Accumulate File "derive/param1.elpi".
Elpi Accumulate Db derive.param1.db.

Elpi Accumulate Db derive.param1.functor.db.
Elpi Accumulate File "derive/param1_functor.elpi".

Elpi Accumulate Db derive.param1.congr.db.
Elpi Accumulate File "derive/param1_congr.elpi".

Elpi Accumulate Db derive.param1.inhab.db.
Elpi Accumulate File "derive/param1_inhab.elpi".

Elpi Accumulate Db derive.param1.trivial.db.
Elpi Accumulate File "derive/param1_trivial.elpi".

Elpi Accumulate Db derive.invert.db.
Elpi Accumulate File "derive/invert.elpi".

Elpi Accumulate Db derive.idx2inv.db.
Elpi Accumulate File "derive/idx2inv.elpi".

Elpi Accumulate Db derive.induction.db.
Elpi Accumulate File "derive/induction.elpi".

Elpi Accumulate Db derive.bcongr.db.
Elpi Accumulate File "ltac/injection.elpi".
Elpi Accumulate File "derive/bcongr.elpi".

Elpi Accumulate Db derive.eqK.db.
Elpi Accumulate File "ltac/discriminate.elpi".
Elpi Accumulate File "derive/eqK.elpi".

Elpi Accumulate Db derive.eqcorrect.db.
Elpi Accumulate File "derive/eqcorrect.elpi".

Elpi Accumulate File "derive/eqOK.elpi".

Elpi Accumulate File "derive/param2.elpi".
Elpi Accumulate Db derive.param2.db.

Elpi Accumulate File "derive/derive.elpi".
Elpi Accumulate lp:{{

% runs P in a context where Coq #[attributes] are parsed
pred with-attributes i:prop.
with-attributes P :-
  attributes A,
  parse-attributes A [att "verbose" bool, att "flat" bool] Opts, !,
  Opts => P.

main [str I, str Prefix] :- !,
    coq.locate I (indt GR),
    with-attributes (derive.main GR Prefix).
  main [str I] :- !,
    coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    with-attributes (derive.main GR Prefix).
  main [indt-decl D] :- !,
    with-attributes (derive.decl+main D).
  main _ :- usage.

  usage :-
    coq.error "Usage:  derive <inductive type> [<prefix>]\n\tderive Inductive name Params : Arity := Constructors.".
}}.
Elpi Typecheck.
Elpi Export derive.
