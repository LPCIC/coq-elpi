(* Generates a module containing all the derived constants.

   license: GNU Lesser General Public License Version 2.1 or later
   ------------------------------------------------------------------------- *)


(* since non-uniform inductive parameters are rarely used and the inference
   code from the kernel is not easily accessible, we require the user to
   be explicit about them, eg Inductive foo U1 U2 | NU1 NU2 := ... *)
#[global] Set Uniform Inductive Parameters.

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
From elpi.apps.derive Extra Dependency "eq.elpi" as eq.
From elpi.apps.derive Extra Dependency "isK.elpi" as isK.
From elpi.apps.derive Extra Dependency "projK.elpi" as projK.
From elpi.apps.derive Extra Dependency "paramX_lib.elpi" as paramX.
From elpi.apps.derive Extra Dependency "param1.elpi" as param1.
From elpi.apps.derive Extra Dependency "param1_functor.elpi" as param1_functor.
From elpi.apps.derive Extra Dependency "param1_congr.elpi" as param1_congr.
From elpi.apps.derive Extra Dependency "param1_inhab.elpi" as param1_inhab.
From elpi.apps.derive Extra Dependency "param1_trivial.elpi" as param1_trivial.
From elpi.apps.derive Extra Dependency "invert.elpi" as invert.
From elpi.apps.derive Extra Dependency "idx2inv.elpi" as idx2inv.
From elpi.apps.derive Extra Dependency "induction.elpi" as induction.
From elpi.apps.derive Extra Dependency "injection.elpi" as injection.
From elpi.apps.derive Extra Dependency "bcongr.elpi" as bcongr.
From elpi.apps.derive Extra Dependency "discriminate.elpi" as discriminate.
From elpi.apps.derive Extra Dependency "eqK.elpi" as eqK.
From elpi.apps.derive Extra Dependency "eqcorrect.elpi" as eqcorrect.
From elpi.apps.derive Extra Dependency "eqOK.elpi" as eqOK.
From elpi.apps.derive Extra Dependency "param2.elpi" as param2.
From elpi.apps.derive Extra Dependency "lens.elpi" as lens.
From elpi.apps.derive Extra Dependency "lens_laws.elpi" as lens_laws.
From elpi.apps.derive Extra Dependency "derive.elpi" as derive.

From elpi.apps Require Export
  derive.eq
  derive.isK
  derive.projK
  derive.param1
  derive.param1_congr
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
Elpi Accumulate File eq.

Elpi Accumulate Db derive.isK.db.
Elpi Accumulate File isK.

Elpi Accumulate Db derive.projK.db.
Elpi Accumulate File projK.

Elpi Accumulate File paramX.

Elpi Accumulate File param1.
Elpi Accumulate Db derive.param1.db.

Elpi Accumulate Db derive.param1.functor.db.
Elpi Accumulate File param1_functor.

Elpi Accumulate Db derive.param1.congr.db.
Elpi Accumulate File param1_congr.

Elpi Accumulate Db derive.param1.trivial.db.
Elpi Accumulate File param1_inhab.
Elpi Accumulate File param1_trivial.

Elpi Accumulate Db derive.invert.db.
Elpi Accumulate File invert.

Elpi Accumulate Db derive.idx2inv.db.
Elpi Accumulate File idx2inv.

Elpi Accumulate Db derive.induction.db.
Elpi Accumulate File induction.

Elpi Accumulate Db derive.bcongr.db.
Elpi Accumulate File injection.
Elpi Accumulate File bcongr.

Elpi Accumulate Db derive.eqK.db.
Elpi Accumulate File discriminate.
Elpi Accumulate File eqK.

Elpi Accumulate Db derive.eqcorrect.db.
Elpi Accumulate File eqcorrect.

Elpi Accumulate File eqOK.

Elpi Accumulate File param2.
Elpi Accumulate Db derive.param2.db.

Elpi Accumulate File lens.
Elpi Accumulate Db derive.lens.db.
Elpi Accumulate File lens_laws.

Elpi Accumulate File derive.
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
  with-attributes (derive.main GR {calc (Prefix ^ "_")} _).

main [str I] :- !,
  coq.locate I (indt GR),
  coq.gref->id (indt GR) Tname,
  main [str I, str Tname].

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
