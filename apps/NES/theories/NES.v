From elpi.apps.NES.elpi Extra Dependency "nes_synterp.elpi" as nes_synterp.
From elpi.apps.NES.elpi Extra Dependency "nes_interp.elpi" as nes_interp.

From elpi Require Import elpi.

#[phase="both"] Elpi Db NES.db lp:{{

typeabbrev path (list string).

:index (2)
pred ns o:list string, o:modpath.

}}.

#[synterp] Elpi Accumulate NES.db lp:{{

pred open-ns o:string, o:list string.
:name "open-ns:begin"
open-ns _ _ :- fail.

}}.

Elpi Command NES.Status.
#[synterp] Elpi Accumulate Db NES.db.
#[synterp] Elpi Accumulate File nes_synterp.
#[synterp] Elpi Accumulate lp:{{

main _ :-
  coq.say "NES: current namespace" {nes.current-path},
  std.findall (ns Y_ Z_) NS,
  coq.say "NES: registered namespaces" NS.

}}.

Elpi Export NES.Status.

Elpi Command NES.Begin.
#[phase="both"] Elpi Accumulate Db NES.db.
#[synterp] Elpi Accumulate File nes_synterp.
#[interp] Elpi Accumulate File nes_interp.
#[synterp] Elpi Accumulate lp:{{

  main [str NS] :- !, nes.begin-path {nes.string->non-empty-ns NS} _.
  main _ :- coq.error "usage: NES.Begin <DotSeparatedPath>".

}}.
#[interp] Elpi Accumulate lp:{{ main _ :- nes.begin-path. }}.

Elpi Export NES.Begin.

Elpi Command NES.End.
#[phase="both"] Elpi Accumulate Db NES.db.
#[synterp] Elpi Accumulate File nes_synterp.
#[interp] Elpi Accumulate File nes_interp.
#[synterp] Elpi Accumulate lp:{{

  main [str NS] :- nes.end-path {nes.string->non-empty-ns NS} _.
  main _ :- coq.error "usage: NES.End <DotSeparatedPath>".

}}.
#[interp] Elpi Accumulate lp:{{ main _ :- nes.end-path. }}.

Elpi Export NES.End.


Elpi Command NES.Open.
#[phase="both"] Elpi Accumulate Db NES.db.
#[synterp] Elpi Accumulate File nes_synterp.
#[interp] Elpi Accumulate File nes_interp.
#[synterp] Elpi Accumulate lp:{{

  main [str NS] :- nes.open-path {nes.resolve NS}.
  main _ :- coq.error "usage: NES.Open <DotSeparatedPath>".

}}.
#[interp] Elpi Accumulate lp:{{ main _ :- nes.open-path. }}.

Elpi Export NES.Open.

(* List the contents a namespace *)
Elpi Command NES.List.
#[phase="both"] Elpi Accumulate Db NES.db.
#[synterp] Elpi Accumulate File nes_synterp.
#[interp] Elpi Accumulate File nes_interp.
#[synterp] Elpi Accumulate lp:{{
  main-synterp [str NS] (pr DB Path) :- nes.resolve NS Path, std.findall (ns O_ P_) DB.
}}.
#[interp] Elpi Accumulate lp:{{
  pred pp-gref i:gref, o:coq.pp.
  pp-gref GR PP :- coq.term->pp (global GR) PP.

  main-interp [str _] (pr DB Path) :- DB => nes.print-path Path pp-gref.
  main _ :- coq.error "usage: NES.List <DotSeparatedPath>".

}}.

Elpi Export NES.List.

(* NES.List with types *)
Elpi Command NES.Print.
#[phase="both"] Elpi Accumulate Db NES.db.
#[synterp] Elpi Accumulate File nes_synterp.
#[interp] Elpi Accumulate File nes_interp.
#[synterp] Elpi Accumulate lp:{{
  main-synterp [str NS] (pr DB Path) :- nes.resolve NS Path, std.findall (ns O_ P_) DB.
}}.
Elpi Accumulate lp:{{
  pred pp-gref i:gref, o:coq.pp.
  pp-gref GR PP :- std.do! [
    coq.env.typeof GR Ty,
    PP = coq.pp.box (coq.pp.hov 2) [
      {coq.term->pp (global GR)}, coq.pp.str " :", coq.pp.spc,
      {coq.term->pp Ty},
    ],
  ].

  main-interp [str _] (pr DB Path) :- DB => nes.print-path Path pp-gref.
  main _ :- coq.error "usage: NES.Print <DotSeparatedPath>".

}}.

Elpi Export NES.Print.
