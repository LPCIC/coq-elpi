From elpi Require Import elpi.
From elpi.apps Require Import tc.

Elpi Tactic TC.TabledSolver.
Elpi TC Solver Register TC.TabledSolver.

Declare ML Module "rocq-elpi.tc-tabled".

From elpi.apps.tc_tabled.elpi Extra Dependency "custom_map.elpi" as custom_map.
From elpi.apps.tc_tabled.elpi Extra Dependency "map2.elpi" as map2.
From elpi.apps.tc_tabled.elpi Extra Dependency "tabled_type_class.elpi" as TabledTC.

Elpi Accumulate File custom_map.
Elpi Accumulate File map2.

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

Elpi Export TC.TabledSolver.
