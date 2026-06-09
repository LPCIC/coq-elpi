From elpi Require Import elpi.

Elpi Db self_cycle_db lp:{{ pred self_cycle. }}.
Fail Elpi Accumulate self_cycle_db Db self_cycle_db.

Elpi Db cycle_a lp:{{ pred cycle_a. }}.
Elpi Db cycle_b lp:{{ pred cycle_b. }}.
Elpi Accumulate cycle_a Db cycle_b.
Fail Elpi Accumulate cycle_b Db cycle_a.
