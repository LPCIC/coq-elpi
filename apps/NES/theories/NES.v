From elpi Require Import elpi.

Elpi Db NES.db lp:{{

pred open-ns o:string, o:list string.
:name "open-ns:begin"
open-ns _ _ :- fail.

typeabbrev path (list string).

pred ns o:path, o:modpath.

}}.

Elpi Command NES.Status.
Elpi Accumulate Db NES.db.
Elpi Accumulate File "elpi/nes.elpi".
Elpi Accumulate lp:{{

main _ :-
  std.map {std.findall (open-ns X_ P_)} open-ns->string Stack,
  coq.say "NES: current namespace" {std.rev Stack},
  std.findall (ns Y_ Z_) NS,
  coq.say "NES: registered namespaces" NS.

}}.
Elpi Typecheck.
Elpi Export NES.Status.

Elpi Command NES.Begin.
Elpi Accumulate Db NES.db.
Elpi Accumulate File "elpi/nes.elpi".
Elpi Accumulate lp:{{


main [str NS] :- std.do! [
  coq.env.current-path CP,
  if (open-ns _ NSCP) (std.assert! (NSCP = CP) "NS: cannot begin a namespace inside a module that is inside a namespace") true,
  string->ns NS RevPath,
  std.map {std.findall (open-ns Y_ P_)} open-ns->string Stack,
  coq.locate-all NS L,
  if (std.do! [
     std.mem L (loc-modpath M),
     coq.modpath->path M MP,
     MP = {std.append CP RevPath}
  ])
    (iter-> [] Stack end-ns, iter<- [] Stack begin-ns)
    true,
  iter<- Stack {std.rev RevPath} begin-ns,
].

main _ :- coq.error "usage: NES.Begin <DotSeparatedPath>".

}}.
Elpi Typecheck.
Elpi Export NES.Begin.

Elpi Command NES.End.
Elpi Accumulate Db NES.db.
Elpi Accumulate File "elpi/nes.elpi".
Elpi Accumulate lp:{{

main [str NS] :- std.do! [
  std.rev {string->ns NS} Path,
  std.map {std.findall (open-ns X_ P_)} open-ns->string Stack,
  std.assert! (std.appendR Path Bottom Stack) "NES: Ending a namespace that is not begun",
  iter-> Bottom Path end-ns,
].

main _ :- coq.error "usage: NES.End [DotSeparatedPath]".

}}.
Elpi Typecheck.
Elpi Export NES.End.


Elpi Command NES.Open.
Elpi Accumulate Db NES.db.
Elpi Accumulate File "elpi/nes.elpi".
Elpi Accumulate lp:{{
main [str NS] :- std.do! [
  string->ns NS RevPath,
  std.rev RevPath Path,
  std.map {std.findall (ns Path M_)} ns->modpath Mods,
  std.spy! (std.forall Mods coq.env.import-module)
].

main _ :- coq.error "usage: NES.Open DotSeparatedPath".

}}.
Elpi Typecheck.
Elpi Export NES.Open.
