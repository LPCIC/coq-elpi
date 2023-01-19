From elpi.apps.NES Extra Dependency "nes.elpi" as nes.

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
Elpi Accumulate File nes.
Elpi Accumulate lp:{{

main _ :-
  coq.say "NES: current namespace" {nes.current-path},
  std.findall (ns Y_ Z_) NS,
  coq.say "NES: registered namespaces" NS.

}}.
Elpi Typecheck.
Elpi Export NES.Status.

Elpi Command NES.Begin.
Elpi Accumulate File nes.
Elpi Accumulate lp:{{

  main [str NS] :- nes.begin-path {nes.string->non-empty-ns NS} _.
  main _ :- coq.error "usage: NES.Begin <DotSeparatedPath>".

}}.
Elpi Accumulate Db NES.db.
Elpi Typecheck.
Elpi Export NES.Begin.

Elpi Command NES.End.
Elpi Accumulate File nes.
Elpi Accumulate lp:{{

  main [str NS] :- nes.end-path {nes.string->non-empty-ns NS} _.
  main _ :- coq.error "usage: NES.End <DotSeparatedPath>".

}}.
Elpi Accumulate Db NES.db.
Elpi Typecheck.
Elpi Export NES.End.


Elpi Command NES.Open.
Elpi Accumulate Db NES.db.
Elpi Accumulate File nes.
Elpi Accumulate lp:{{

  main [str NS] :- nes.open-path {nes.resolve NS}.
  main _ :- coq.error "usage: NES.Open <DotSeparatedPath>".

}}.
Elpi Typecheck.
Elpi Export NES.Open.

(* List the contents a namespace *)
Elpi Command NES.List.
Elpi Accumulate Db NES.db.
Elpi Accumulate File nes.
Elpi Accumulate lp:{{

  pred pp-gref i:gref, o:coq.pp.
  pp-gref GR PP :- coq.term->pp (global GR) PP.

  main [str NS] :- nes.print-path {nes.resolve NS} pp-gref.
  main _ :- coq.error "usage: NES.List <DotSeparatedPath>".

}}.
Elpi Typecheck.
Elpi Export NES.List.

(* NES.List with types *)
Elpi Command NES.Print.
Elpi Accumulate Db NES.db.
Elpi Accumulate File nes.
Elpi Accumulate lp:{{

  pred pp-gref i:gref, o:coq.pp.
  pp-gref GR PP :- std.do! [
    coq.env.typeof GR Ty,
    PP = coq.pp.box (coq.pp.hov 2) [
      {coq.term->pp (global GR)}, coq.pp.str " :", coq.pp.spc,
      {coq.term->pp Ty},
    ],
  ].

  main [str NS] :- nes.print-path {nes.resolve NS} pp-gref.
  main _ :- coq.error "usage: NES.Print <DotSeparatedPath>".

}}.
Elpi Typecheck.
Elpi Export NES.Print.
