Require Import elpi.elpi.
From elpi.tests Extra Dependency "test_recompile_section_bug_file.elpi" as file.

Elpi Command foo.
Elpi Accumulate File file.

Elpi Accumulate lp:{{/*(*/
main _.
/*)*/}}.

Elpi Export foo.
