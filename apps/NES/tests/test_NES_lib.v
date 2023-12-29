From elpi.apps.NES Extra Dependency "nes_synterp.elpi" as nes_synterp.
From elpi.apps Require Import NES.

Elpi Command Make.
#[synterp] Elpi Accumulate Db NES.db.
#[synterp] Elpi Accumulate File nes_synterp.
#[synterp] Elpi Accumulate lp:{{

  main-synterp [str Path] ActionsToOpen :- std.do! [
    nes.string->ns Path NS,
    nes.begin-path NS OpenNS,
    coq.synterp-actions ActionsToOpen,
    OpenNS => nes.end-path NS _NewNS,
  ].
  main _ :- coq.error "usage: Make <DotSeparatedPath>".

}}.
#[interp] Elpi Accumulate lp:{{
  main-interp [str _] ActionsBefore :- std.do! [
    std.forall ActionsBefore coq.replay-synterp-action,
    coq.env.add-const "x" {{ 42 }} _ @transparent! _C,
    coq.replay-all-missing-synterp-actions,
  ].
}}.
Elpi Typecheck.
Elpi Export Make.

Make Cats.And.Dogs.
Print Cats.And.Dogs.x.
