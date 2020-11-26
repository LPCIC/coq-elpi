From elpi Require Import elpi.

Elpi Db NES.db lp:{{

pred open-ns o:string, o:list string.
:name "open-ns:begin"
open-ns _ _ :- fail.

typeabbrev path (list string).

:index (2)
pred ns o:path, o:modpath.

}}.

Elpi Command NES.Status.
Elpi Accumulate Db NES.db.
Elpi Accumulate File "elpi/nes.elpi".
Elpi Accumulate lp:{{

main _ :-
  std.map {std.findall (open-ns X_ P_)} nes.open-ns->string Stack,
  coq.say "NES: current namespace" {nes.join "." {std.rev Stack} },
  std.findall (ns Y_ Z_) NS,
  coq.say "NES: registered namespaces" NS.

}}.
Elpi Typecheck.
Elpi Export NES.Status.

Elpi Command NES.Begin.
Elpi Accumulate File "elpi/nes.elpi".
Elpi Accumulate lp:{{

  main [str NS] :- nes.begin-path {nes.string->ns NS}.
  main _ :- coq.error "usage: NES.Begin <DotSeparatedPath>".

}}.
Elpi Accumulate Db NES.db.
Elpi Typecheck.
Elpi Export NES.Begin.

Elpi Command NES.End.
Elpi Accumulate File "elpi/nes.elpi".
Elpi Accumulate lp:{{

  main [str NS] :- nes.end-path {nes.string->ns NS}.
  main _ :- coq.error "usage: NES.End <DotSeparatedPath>".

}}.
Elpi Accumulate Db NES.db.
Elpi Typecheck.
Elpi Export NES.End.


Elpi Command NES.Open.
Elpi Accumulate Db NES.db.
Elpi Accumulate File "elpi/nes.elpi".
Elpi Accumulate lp:{{

  main [str NS] :- nes.open-path {nes.string->ns NS}.
  main _ :- coq.error "usage: NES.Open <DotSeparatedPath>".

}}.
Elpi Typecheck.
Elpi Export NES.Open.
