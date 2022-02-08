(* Generates a module containing all the derived constants.

   license: GNU Lesser General Public License Version 2.1 or later
   ------------------------------------------------------------------------- *)

(** The derive command
   The derive command can be invoked in two ways.
   - [derive <inductive-type> <prefix>]
   - [derive Inductive <declaration>]
     [derive Record <declaration>]

   The first command runs all the derivations on an alerady declared inductive
   type named [<inductive-type>] and all generated constants are named after the
   prefix [<prefix>] (by default the inductive type name followed by [_]). Example:

<<
      derive nat. (* default prefix nat_ *)
      derive nat my_nat_stuff_.
>>

   The second command takes as argument an inductive type declaration, it
   creates a module named after the inductive type and puts inside id both
   the inductive types and the output of the derivations. Example:

<<
     derive Inductive tickle A := stop | more : A -> tickle-> tickle.
>>

   is equivalent to

<<
     Module tickle.
     Inductive tickle A := stop | more : A -> tickle-> tickle.
     derive tickle "".
     End tickle.
     Notation tickle := tickle.tickle.
     Notation stop := tickle.stop.
     Notation more := tickle.more.
>>

  Both commands honor the [#[verbose]] attribute. If set they print all
  the derivations that are run, and if they fail or succeed.

  A derivation d can be skipped by using the [#[skip(d)]] attribute.
  A derivation different from d can be skipped [#[only(d)]] attribute.

*)

From elpi.apps Require Export
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
  derive.lens
  derive.lens_laws
.

Elpi Command derive.

Elpi Accumulate Db derive.eq.db.
Elpi Accumulate File "eq.elpi" From elpi.apps.derive.

Elpi Accumulate Db derive.isK.db.
Elpi Accumulate File "isK.elpi" From elpi.apps.derive.

Elpi Accumulate Db derive.map.db.
Elpi Accumulate File "map.elpi" From elpi.apps.derive.

Elpi Accumulate Db derive.projK.db.
Elpi Accumulate File "projK.elpi" From elpi.apps.derive.

Elpi Accumulate File "paramX-lib.elpi" From elpi.apps.derive.

Elpi Accumulate File "param1.elpi" From elpi.apps.derive.
Elpi Accumulate Db derive.param1.db.

Elpi Accumulate Db derive.param1.functor.db.
Elpi Accumulate File "param1_functor.elpi" From elpi.apps.derive.

Elpi Accumulate Db derive.param1.congr.db.
Elpi Accumulate File "param1_congr.elpi" From elpi.apps.derive.

Elpi Accumulate Db derive.param1.inhab.db.
Elpi Accumulate File "param1_inhab.elpi" From elpi.apps.derive.

Elpi Accumulate Db derive.param1.trivial.db.
Elpi Accumulate File "param1_trivial.elpi" From elpi.apps.derive.

Elpi Accumulate Db derive.invert.db.
Elpi Accumulate File "invert.elpi" From elpi.apps.derive.

Elpi Accumulate Db derive.idx2inv.db.
Elpi Accumulate File "idx2inv.elpi" From elpi.apps.derive.

Elpi Accumulate Db derive.induction.db.
Elpi Accumulate File "induction.elpi" From elpi.apps.derive.

Elpi Accumulate Db derive.bcongr.db.
Elpi Accumulate File "injection.elpi" From elpi.apps.derive.
Elpi Accumulate File "bcongr.elpi" From elpi.apps.derive.

Elpi Accumulate Db derive.eqK.db.
Elpi Accumulate File "discriminate.elpi" From elpi.apps.derive.
Elpi Accumulate File "eqK.elpi" From elpi.apps.derive.

Elpi Accumulate Db derive.eqcorrect.db.
Elpi Accumulate File "eqcorrect.elpi" From elpi.apps.derive.

Elpi Accumulate File "eqOK.elpi" From elpi.apps.derive.

Elpi Accumulate File "param2.elpi" From elpi.apps.derive.
Elpi Accumulate Db derive.param2.db.

Elpi Accumulate File "lens.elpi" From elpi.apps.derive.
Elpi Accumulate Db derive.lens.db.
Elpi Accumulate File "lens_laws.elpi" From elpi.apps.derive.

Elpi Accumulate File "derive.elpi" From elpi.apps.derive.
Elpi Accumulate lp:{{

% runs P in a context where Coq #[attributes] are parsed
pred with-attributes i:prop.
with-attributes P :-
  attributes A,
  coq.parse-attributes A [
    att "verbose" bool,
    att "only" attmap,
  ] Opts, !,
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

(* we derive the Coq prelude *)

Module Prelude.
Module Empty_set. derive Init.Datatypes.Empty_set "". End Empty_set.
Module unit. derive Init.Datatypes.unit "". End unit.
Module bool. derive Init.Datatypes.bool "". End bool.
Module nat. derive Init.Datatypes.nat "". End nat.
Module option. derive Init.Datatypes.option "". End option.
Module sum. derive Init.Datatypes.sum "". End sum.
Module prod. derive Init.Datatypes.prod "". End prod.
Module list. derive Init.Datatypes.list "". End list.
Module comparison. derive Init.Datatypes.comparison "". End comparison.
End Prelude.

Export Prelude.
