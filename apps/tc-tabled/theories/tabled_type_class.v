From elpi Require Import elpi.
From elpi.apps Require Import tc.

Elpi Tactic TC.TabledSolver.
Elpi TC Solver Register TC.TabledSolver.

Declare ML Module "rocq-elpi.tc-tabled".

From elpi.apps.tc_tabled.elpi Extra Dependency "custom_map.elpi" as custom_map.
From elpi.apps.tc_tabled.elpi Extra Dependency "map2.elpi" as map2.
From elpi.apps.tc_tabled.elpi Extra Dependency "tabled_type_class.elpi" as TabledTC.
From elpi.apps.tc_tabled.elpi Extra Dependency "avl.elpi" as avl.

Elpi Accumulate File custom_map.
Elpi Accumulate File map2.
Elpi Accumulate File avl.

Elpi Accumulate lp:{{
  pred mymap_make i:(pred i:K, i:K, o:cmp), o:mymap K V.
  pred mymap_find i:K i:(mymap K V) o:V.
  pred mymap_add i:K i:V i:(mymap K V) o:(mymap K V).
  pred mymap_update i:K i:V i:(mymap K V) o:(mymap K V).

  /*
  typeabbrev (mymap K V) (custom_map K V).

  mymap_make Cmp M :- custom_make Cmp M.
  mymap_find K M V :- custom_find K M V.
  mymap_add K V M M1 :- custom_add K V M M1.
  mymap_update K V M M1 :- custom_add K V M M1.
  */

  typeabbrev (mymap K V) (std.map2 K V).

  mymap_make Cmp M :- std.map2.make Cmp M.
  mymap_find K M V :- std.map2.find K M V.
  mymap_add K V M M1 :- std.map2.add K V M M1.
  mymap_update K V M M1 :- std.map2.update K V M M1.

  /*
  typeabbrev (mymap K V) (avl.tree K V).

  mymap_make Cmp M :- avl.empty Cmp M.
  mymap_find K M V :- avl.lookup_node K M V.
  mymap_add K V M M1 :- avl.insert_node K V M M1.
  mymap_update K V M M1 :- avl.update_node K V M M1.
  */
}}.

Elpi Accumulate File TabledTC.

(* Slow map test *)
Elpi Accumulate lp:{{
  pred map_test_fold i:int i:V i:V o:mymap int V.
  map_test_fold I V U M :-
    std.fold
      {std.iota I}
      {std.fold
        {std.iota I}
        {mymap_make cmp_term}
        (k\m\ mymap_add k V m)
      }
      (k\m\ mymap_update k U m)
      M
    .
}}.

(* Elpi Accumulate lp:{{ *)
(*   pred map_test_fold i:int, i:V, i:V, o:std.map int V. *)
(*   map_test_fold I V U M :- *)
(*    std.fold *)
(*      {std.iota I} *)
(*      {std.map.make cmp_term} *)
(*      (k\m\ std.map.add k V m) /* insert */ *)
(*      Mtemp, *)
(*     std.fold *)
(*       {std.iota I} *)
(*       Mtemp *)
(*       (k\m\ std.map.add k U m) /* update */ *)
(*       M *)
(*     . *)
(* }}. *)

(* Time Elpi Query lp:{{ *)
(*   map_test_fold 6000 *)
(*     {std.iota 20} *)
(*     {std.iota 19} _. *)
(* }}. *)

Time Elpi Query lp:{{
  map_test_fold 2000 {std.iota 20} {std.iota 19} _
  .
}}.

(* Time Elpi Query lp:{{ *)
(*   map_test_fold 6000 {std.iota 20} {std.iota 19} _ *)
(*   . *)
(* }}. *)

(* Time Elpi Query lp:{{ *)
(*   map_test_fold 7000 {std.iota 20} {std.iota 19} _ *)
(*   . *)
(* }}. *)

(* Time Elpi Query lp:{{ *)
(*   map_test_fold 8000 {std.iota 20} {std.iota 19} _ *)
(*   . *)
(* }}. *)

(* Time Elpi Query lp:{{ *)
(*   map_test_fold 9000 {std.iota 20} {std.iota 19} _ *)
(*   . *)
(* }}. *)

(* Time Elpi Query lp:{{ *)
(*   map_test_fold 10000 {std.iota 20} {std.iota 19} _ *)
(*   . *)
(* }}. *)

(* Time Elpi Query lp:{{ *)
(*   map_test_fold 11000 {std.iota 20} {std.iota 19} _ *)
(*   . *)
(* }}. *)

(* Time Elpi Query lp:{{ *)
(*   map_test_fold 12000 {std.iota 20} {std.iota 19} _ *)
(*   . *)
(* }}. *)

(* Time Elpi Query lp:{{ *)
(*   map_test_fold 13000 {std.iota 20} {std.iota 19} _ *)
(*   . *)
(* }}. *)

(* Time Elpi Query lp:{{ *)
(*   map_test_fold 14000 {std.iota 20} {std.iota 19} _ *)
(*   . *)
(* }}. *)

(* Time Elpi Query lp:{{ *)
(*   map_test_fold 28000 {std.iota 20} {std.iota 19} _ *)
(*   . *)
(* }}. *)

Elpi Query lp:{{
  coq.say "".
}}.

Elpi Export TC.TabledSolver.

(* 6000: Finished transaction in 7.498 secs (7.454u,0.042s) (successful) *)
(* 7000: Finished transaction in 11.687 secs (11.666u,0.003s) (successful) *)
(* 8000: Finished transaction in 13.516 secs (13.502u,0.002s) (successful) *)
(* 9000: Finished transaction in 16.214 secs (16.206u,0.002s) (successful) *)
(* 10000: Finished transaction in 19.843 secs (19.817u,0.016s) (successful) *)
(* 11000: Finished transaction in 24.429 secs (24.396u,0.002s) (successful) *)
(* 12000: Finished transaction in 24.807 secs (24.791u,0.002s) (successful) *)
(* 13000: Finished transaction in 32.366 secs (32.341u,0.008s) (successful) *)
(* 14000: Finished transaction in 38.164 secs (38.044u,0.006s) (successful) *)

(* Finished transaction in 37.175 secs (37.039u,0.128s) (successful) *)
(* Finished transaction in 45.125 secs (45.017u,0.103s) (successful) *)
(* Finished transaction in 58.736 secs (58.705u,0.026s) (successful) *)
(* Finished transaction in 75.953 secs (75.914u,0.033s) (successful) *)
(* Finished transaction in 97.66 secs (97.576u,0.075s) (successful) *)
(* Finished transaction in 120.093 secs (120.063u,0.017s) (successful) *)
(* Finished transaction in 147.584 secs (147.567u,0.001s) (successful) *)
(* Finished transaction in 168.396 secs (168.328u,0.056s) (successful) *)
(* Finished transaction in 197.791 secs (197.718u,0.057s) (successful) *)

(* 3200 secs ~ 1 hour *)
(* 866 secs ~ 14.5 min *)

(* (6,37.175), (7,45.125), (8,58.736), (9,75.953), (10,97.66), (11,120.093), (12,147.584), (13,168.396), (14,197.791) *)
(* 1.23069 x^2 - 4.04515 x + 14.5688 , R = 0.997845 *)


(* 28000 *)
