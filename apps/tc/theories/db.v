(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

From elpi Require Import elpi.

From elpi.apps.tc.elpi Extra Dependency "base.elpi" as base.
From elpi.apps.tc.elpi Extra Dependency "tc_options.db.elpi" as tc_optionsdb.
From elpi.apps.tc.elpi Extra Dependency "tc.db.elpi" as tcdb.

(* 
  tc_option.db contains the set of options used by the solver of tc. 
  all the options are set to false by default
*)
Elpi Db tc_options.db lp:{{ accumulate "elpi.apps.tc.elpi/tc_options.db". }}.

Elpi Db tc.db lp:{{ accumulate "elpi.apps.tc.elpi/tc.db". }}.
