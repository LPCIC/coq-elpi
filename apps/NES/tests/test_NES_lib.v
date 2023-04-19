From elpi.apps.NES Extra Dependency "nes.elpi" as nes.
From elpi.apps Require Import NES.

Elpi Command Make.
Elpi Accumulate Db NES.db.
Elpi Accumulate File nes.
Elpi Accumulate lp:{{

  main [str Path] :- std.do! [
    nes.string->ns Path NS,
    nes.begin-path NS OpenNS,
    OpenNS => std.do! [
      coq.env.add-const "x" {{ 42 }} _ @transparent! _C,
      nes.end-path NS _NewNS,
    ],
  ].
  main _ :- coq.error "usage: Make <DotSeparatedPath>".

}}.
Elpi Typecheck.
Elpi Export Make.

Make Cats.And.Dogs.
