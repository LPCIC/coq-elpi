Require Import elpi.elpi.
Require Import elpi.tests.test_recompile_section_bug_cmd.

Section Test1.
  foo.                          (* Recompiles everything, as expected for first use *)
End Test1.

Section Test2.
  foo.                          (* Recompiles everything again! *)
End Test2.

foo.                            (* Recompiles everything again! *)
foo.                            (* No longer recompiles anything. *)

Section Test3.
  foo.                          (* No longer recompiles anything. *)
End Test3.
