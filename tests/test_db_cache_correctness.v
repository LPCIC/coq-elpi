From elpi Require Import elpi.

(* DB references are dynamic: a cached importer must see later changes in the
   imported DB. *)
Elpi Db cache_stale_source lp:{{ pred cache_stale_p o:int. }}.
Elpi Accumulate cache_stale_source lp:{{ cache_stale_p 0. }}.

Elpi Db cache_stale_target lp:{{ }}.
Elpi Accumulate cache_stale_target Db cache_stale_source.
Elpi Query cache_stale_target lp:{{ cache_stale_p 0. }}.

Elpi Program cache_stale_program lp:{{ }}.
Elpi Accumulate cache_stale_program Db cache_stale_source.
Elpi Query cache_stale_program lp:{{ cache_stale_p 0. }}.

Elpi Accumulate cache_stale_source lp:{{ cache_stale_p 1. }}.
Elpi Query cache_stale_target lp:{{ cache_stale_p 1. }}.
Elpi Query cache_stale_program lp:{{ cache_stale_p 1. }}.

(* Shared DB dependencies should be compiled once per context: importing two
   DBs that both import the same dependency must not duplicate its units. *)
Elpi Db cache_shared_common lp:{{ pred cache_shared_p. cache_shared_p. }}.
Elpi Db cache_shared_left lp:{{ pred cache_left_p. cache_left_p. }}.
Elpi Db cache_shared_right lp:{{ pred cache_right_p. cache_right_p. }}.
Elpi Accumulate cache_shared_left Db cache_shared_common.
Elpi Accumulate cache_shared_right Db cache_shared_common.

Elpi Db cache_shared_join lp:{{ }}.
Elpi Accumulate cache_shared_join Db cache_shared_left.
Elpi Accumulate cache_shared_join Db cache_shared_right.
Elpi Query cache_shared_join lp:{{ cache_shared_p, cache_left_p, cache_right_p. }}.
