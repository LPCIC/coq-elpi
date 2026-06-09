From elpi Require Import elpi.

(* Accumulating a signature must not prevent a later accumulation of the
   corresponding full compilation unit: signatures declare predicates, but do
   not contain their clauses. *)
Elpi Program sig_then_full_program lp:{{ }}.
Elpi File sig_then_full_program_file lp:{{
  pred q.
  q.
}}.
Elpi Accumulate sig_then_full_program File Signature sig_then_full_program_file.
Elpi Accumulate sig_then_full_program File sig_then_full_program_file.
Elpi Query sig_then_full_program lp:{{ q. }}.

(* Same regression for databases. *)
Elpi Db sig_then_full_db lp:{{ }}.
Elpi File sig_then_full_db_file lp:{{
  pred r.
  r.
}}.
Elpi Accumulate sig_then_full_db File Signature sig_then_full_db_file.
Elpi Accumulate sig_then_full_db File sig_then_full_db_file.
Elpi Query sig_then_full_db lp:{{ r. }}.
