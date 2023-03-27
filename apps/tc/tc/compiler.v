From elpi Require Import elpi.
From elpi.apps Require Import tc.instances_db.
From elpi.apps.tc Extra Dependency "compiler.elpi" as compiler.
From elpi.apps.tc Extra Dependency "parserAPI.elpi" as parserAPI.

Elpi Command add_instances.

Set Warnings "+elpi".

Elpi Accumulate Db tc.db.
Elpi Accumulate File compiler.
Elpi Accumulate File parserAPI.
Elpi Typecheck.
