
From elpi Require Import elpi.

From elpi.tests Extra Dependency "file1.elpi" as file1.
From elpi.tests Extra Dependency "file2.elpi" as file2.

Elpi File f1 lp:{{ accumulate "elpi.tests/file1". }}.
Elpi File f2 lp:{{ accumulate "elpi.tests/file2". }}.

Elpi Db db lp:{{ }}.
Elpi Accumulate db File f1.
Elpi Accumulate db File f2.

Elpi Command test.
Elpi Accumulate Db db.
Elpi Print test "elpi.tests/xx".

