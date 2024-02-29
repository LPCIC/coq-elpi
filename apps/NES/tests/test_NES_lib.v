From elpi.apps.NES Extra Dependency "nes_synterp.elpi" as nes_synterp.
From elpi.apps.NES Extra Dependency "nes_interp.elpi" as nes_interp.
From elpi.apps Require Import NES.

Elpi Command Make.
#[phase="both"] Elpi Accumulate Db NES.db.
#[synterp] Elpi Accumulate File nes_synterp.
#[interp] Elpi Accumulate File nes_interp.
#[synterp] Elpi Accumulate lp:{{

  main [str Path] :- std.do! [
    nes.string->ns Path NS,
    nes.begin-path NS OpenNS,
    OpenNS => nes.end-path NS _NewNS,
  ].
  main _ :- coq.error "usage: Make <DotSeparatedPath>".

}}.
#[interp] Elpi Accumulate lp:{{
  main _ :- std.do! [
    nes.begin-path,
    coq.env.add-const "x" {{ 42 }} _ @transparent! _C,
    nes.end-path,
  ].
}}.
Elpi Typecheck.
Elpi Export Make.

Make Cats.And.Dogs.
Print Cats.And.Dogs.x.
