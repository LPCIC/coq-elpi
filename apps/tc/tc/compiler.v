From elpi Require Import elpi.
From elpi.apps Require Import tc.instances_db.
From elpi.apps.tc Extra Dependency "compiler.elpi" as compiler.
From elpi.apps.tc Extra Dependency "parserAPI.elpi" as parserAPI.
From elpi.apps.tc Extra Dependency "modes.elpi" as modes.

Set Warnings "+elpi".

Elpi Command add_instances.
Elpi Accumulate Db tc.db.
Elpi Accumulate File modes.
Elpi Accumulate File compiler.
Elpi Accumulate File parserAPI.
Elpi Typecheck.
