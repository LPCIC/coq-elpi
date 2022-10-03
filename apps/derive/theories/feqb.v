(* Generates a module containing all the derived constants.

   license: GNU Lesser General Public License Version 2.1 or later
   ------------------------------------------------------------------------- *)


(* since non-uniform inductive parameters are rarely used and the inference
   code from the kernel is not easily accessible, we require the user to
   be explicit about them, eg Inductive foo U1 U2 | NU1 NU2 := ... *)
#[global] Set Uniform Inductive Parameters.

(** The feqb command
   The feqb command can be invoked in two ways.
   - [feqb <inductive-type> <prefix>]
   - [feqb Inductive <declaration>]
     [feqb Record <declaration>]

   The first command runs all the derivations on an alerady declared inductive
   type named [<inductive-type>] and all generated constants are named after the
   prefix [<prefix>] (by default the inductive type name followed by [_]). Example:

<<
      feqb nat. (* default prefix nat_ *)
      feqb nat my_nat_stuff_.
>>

   The second command takes as argument an inductive type declaration, it
   creates a module named after the inductive type and puts inside id both
   the inductive types and the output of the derivations. Example:

<<
     feqb Inductive tickle A := stop | more : A -> tickle-> tickle.
>>

   is equivalent to

<<
     Module tickle.
     Inductive tickle A := stop | more : A -> tickle-> tickle.
     feqb tickle "".
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
From elpi.apps.derive Extra Dependency "paramX_lib.elpi" as paramX.
From elpi.apps.derive Extra Dependency "param1.elpi" as param1.
From elpi.apps.derive Extra Dependency "param1_functor.elpi" as param1_functor.
From elpi.apps.derive Extra Dependency "param1_inhab.elpi" as param1_inhab.
From elpi.apps.derive Extra Dependency "param1_trivial.elpi" as param1_trivial.
From elpi.apps.derive Extra Dependency "induction.elpi" as induction.
From elpi.apps.derive Extra Dependency "tag.elpi" as tag.
From elpi.apps.derive Extra Dependency "fields.elpi" as fields.
From elpi.apps.derive Extra Dependency "eqb.elpi" as eqb.
From elpi.apps.derive Extra Dependency "eqType.elpi" as eqType.
From elpi.apps.derive Extra Dependency "eqbcorrect.elpi" as eqbcorrect.

From elpi.apps.derive Extra Dependency "feqb.elpi" as feqb.

From elpi.apps Require Export
  derive.param1
  derive.param1_congr
  derive.param1_trivial
  derive.induction
  derive.eqb_core_defs
  derive.tag
  derive.fields
  derive.eqb
  derive.eqbcorrect
.

Elpi Command feqb.

Elpi Accumulate File paramX.

Elpi Accumulate File param1.
Elpi Accumulate Db derive.param1.db.

Elpi Accumulate Db derive.param1.functor.db.
Elpi Accumulate File param1_functor.

Elpi Accumulate Db derive.param1.trivial.db.
Elpi Accumulate File param1_inhab.
Elpi Accumulate File param1_trivial.

Elpi Accumulate Db derive.induction.db.
Elpi Accumulate File induction.

Elpi Accumulate Db derive.eqType.db.
Import PArith.
Local Open Scope positive_scope.
Elpi Accumulate Db derive.tag.db.
Elpi Accumulate File tag.
Elpi Accumulate Db derive.fields.db.
Elpi Accumulate File fields.
Elpi Accumulate Db derive.eqb.db.
Elpi Accumulate File eqb.
Elpi Accumulate File eqType.
Elpi Accumulate Db derive.eqbcorrect.db.
Elpi Accumulate File eqbcorrect.
Close Scope positive_scope.

Elpi Accumulate File feqb.

Elpi Accumulate lp:{{

% runs P in a context where Coq #[attributes] are parsed
pred with-attributes i:prop.
with-attributes P :-
  attributes A,
  coq.parse-attributes A [
    att "verbose" bool,
  ] Opts, !,
  Opts => P.

main [str I, str Prefix] :-
  coq.locate I (indt GR), !,
  with-attributes (feqb.main GR {calc (Prefix ^ "_")} _).

main [str I] :-
  coq.locate I (indt GR), !,
  coq.gref->id (indt GR) Tname,
  main [str I, str Tname].

main [indt-decl D] :- !,
  with-attributes (feqb.decl+main D).

main _ :- usage.

usage :-
  coq.error "Usage:  feqb <inductive type> [<prefix>]\n\nfeqb Inductive name Params : Arity := Constructors.".

}}.
Elpi Typecheck.
Elpi Export feqb.

(* we derive the Coq prelude *)

Module Prelude.
Module Empty_set. feqb Init.Datatypes.Empty_set "". End Empty_set.
Module unit. feqb Init.Datatypes.unit "". End unit.
Module bool. feqb Init.Datatypes.bool "". End bool.
Module nat. feqb Init.Datatypes.nat "". End nat.
Module option. feqb Init.Datatypes.option "". End option.
Module sum. feqb Init.Datatypes.sum "". End sum.
Module prod. feqb Init.Datatypes.prod "". End prod.
Module list. feqb Init.Datatypes.list "". End list.
Module comparison. feqb Init.Datatypes.comparison "". End comparison.
End Prelude.

Export Prelude.
