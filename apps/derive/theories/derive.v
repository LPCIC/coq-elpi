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

From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.
From elpi.apps.derive.elpi Extra Dependency "derive.elpi" as derive.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp.elpi" as derive_synterp.

From elpi Require Import elpi.

Elpi Command derive.

#[phase="both"]
Elpi Accumulate lp:{{
  % runs P in a context where Coq #[attributes] are parsed
  pred with-attributes i:prop.
  with-attributes P :-
    attributes A,
    coq.parse-attributes A [
      att "verbose" bool,
      att "only" attmap,
      att "recursive" bool,
      att "prefix" string,
      att "module" string,
      att "no_alias" bool,
    ] Opts, !,
    Opts => P.

  pred get_name i:indt-decl, o:string.
  get_name (parameter _ _ _ F) N :- pi p\ get_name (F p) N.
  get_name (inductive N _ _ _) N.
  get_name (record N _ _ _) N.
}}.

#[synterp] Elpi Accumulate File derive_synterp_hook.
#[synterp] Elpi Accumulate File derive_synterp.
#[synterp] Elpi Accumulate lp:{{
  main [str TypeName] :- !,
    with-attributes (derive.main TypeName).

  main [indt-decl D] :- !,
    get_name D TypeName,
    with-attributes (derive.main TypeName).

  main _.
}}.

Elpi Accumulate File derive_hook.
Elpi Accumulate File derive.
Elpi Accumulate lp:{{
  main [str I] :- !,
    coq.locate I GR,
    with-attributes (derive.main GR _).

  main [indt-decl D] :- !,
    get_name D TypeName,
    with-attributes (derive.decl+main TypeName D).

  main _ :- usage.

  usage :-
    coq.error "Usage:  derive <inductive type/definition>\n\tderive Inductive name Params : Arity := Constructors.".
}}.


Elpi Export derive.
