From elpi Require Import elpi.

Elpi Db NS.db lp:{{

kind nesting type.
type nested nesting.
type toplevel nesting.


pred open-ns o:string, o:list string.
:name "open-ns:begin"
open-ns _ _ :- fail.

typeabbrev path (list string).

pred ns o:path, o:modpath.

pred ns->modpath i:prop, o:modpath.
ns->modpath (ns _ M) M.

pred open-ns->string i:prop, o:string.
open-ns->string (open-ns S _) S.

pred begin-ns i:string, i:list string.
begin-ns NS Path :-
  if (Path = [])
     (Fresh is NS ^ "_aux_" ^ {std.any->string {new_int} }, coq.env.begin-module Fresh none)
     true,
  coq.env.begin-module NS none,
  coq.env.current-path CP,
  @local! => coq.elpi.accumulate current "NS.db" (clause _ (after "open-ns:begin") (open-ns NS CP)).

pred subpath i:list string, i:prop.
subpath Path (ns Sub _) :- std.appendR _Prefix Path Sub.

pred submod i:modpath, i:prop.
submod Mod (ns _ SubMod) :-
  coq.modpath->path SubMod SubPath,
  coq.modpath->path Mod ModPath,
  std.appendR ModPath _Suffix SubPath.

pred undup i:list A, i:list A, o:list A.
undup [] _ [].
undup [X|XS] Seen YS :- std.mem! Seen X, !, undup XS Seen YS.
undup [X|XS] Seen [X|YS] :- undup XS [X|Seen] YS.

pred end-ns i:string, i:list string.
end-ns NS Path :- std.do! [
  std.findall (ns Path_ M_) AllNS,
  coq.env.end-module M,
  % stuff inside M
  std.filter AllNS (submod M) SubmodNS,
  % since the current program still sees the clauses that will be dropped
  % after closing M
  undup SubmodNS [] SubmodNSNodup,

  coq.locate-module NS M,
  if (Path = []) (coq.env.end-module M_aux, coq.env.export-module M_aux, Local = @global!) (Local = @local!),
  % NS.Open can put clauses in scope
  std.forall [ns [NS|Path] M | SubmodNSNodup]
    (c\ Local => coq.elpi.accumulate current "NS.db" (clause _ _ c)),
].

pred iter-> i:list A, i:list A, i:(A -> list A -> prop).
iter-> _ [] _ :- coq.error "No elements".
iter-> INIT [X] F :- !, F X INIT.
iter-> INIT [X|XS] F :- F X {std.append XS INIT}, iter-> INIT XS F.

pred iter<- i:list A, i:list A, i:(A -> list A -> prop).
iter<- _ [] _ :- coq.error "No elements".
iter<- INIT [X] F :- !, F X INIT.
iter<- INIT [X|XS] F :- iter<- INIT XS F, F X {std.append XS INIT}.

pred string->ns i:string, o:list string.
string->ns S L :- rex_split "\\." S L.

}}.

Elpi Command NS.Status.
Elpi Accumulate Db NS.db.
Elpi Accumulate lp:{{

main _ :-
  std.map {std.findall (open-ns X_ P_)} open-ns->string Stack,
  coq.say "NS: current namespace" {std.rev Stack},
  std.map {std.findall (ns Y_ Z_)} ns->modpath NS,
  coq.say "NS: registered namespaces" NS.

}}.
Elpi Typecheck.
Elpi Export NS.Status.

Elpi Command NS.Begin.
Elpi Accumulate Db NS.db.
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

main _ :- coq.error "usage: NS.Begin <DotSeparatedPath>".

}}.
Elpi Typecheck.
Elpi Export NS.Begin.

Elpi Command NS.End.
Elpi Accumulate Db NS.db.
Elpi Accumulate lp:{{

main [str NS] :- std.do! [
  std.rev {string->ns NS} Path,
  std.map {std.findall (open-ns X_ P_)} open-ns->string Stack,
  std.assert! (std.appendR Path Bottom Stack) "Ending a namespace that is not begun",
  iter-> Bottom Path end-ns,
].

main _ :- coq.error "usage: NS.End [DotSeparatedPath]".

}}.
Elpi Typecheck.
Elpi Export NS.End.


Elpi Command NS.Open.
Elpi Accumulate Db NS.db.
Elpi Accumulate lp:{{
main [str NS] :- std.do! [
  string->ns NS RevPath,
  std.rev RevPath Path,
  std.map {std.findall (ns Path M_)} ns->modpath Mods,
  std.forall Mods coq.env.import-module
].

main _ :- coq.error "usage: NS.Open SpaceSeparatedPath".

}}.
Elpi Typecheck.
Elpi Export NS.Open.


(*********************** TEST *************************)

(* name space creation *)
NS.Begin Foo.
Definition x := 3.
NS.End Foo.
Print Foo.x.

(* adding one name inside an existing name space *)
NS.Begin Foo.
Definition x2 := 4.
NS.End Foo.
Print Foo.x.
Print Foo.x2.

(* shadowing: adding the same name twice *)
NS.Begin Foo.
Definition x := 5.
NS.End Foo.
Check (refl_equal _ : Foo.x = 5). (* shadowing *)

(* nesting *)
NS.Begin A.
NS.Begin B.
Definition c := 1.
NS.End B.
NS.End A.
About A.B.c.

(* adding one name inside an existing, nested, name space *)
NS.Begin A1.
NS.Begin B1.
Definition c := 1.
NS.End B1.
NS.Begin B1.
Definition d := 1.
NS.End B1.
NS.End A1.
About A1.B1.d.
About A1.B1.c.

(* all names in the Foo namespace must be visible *)
NS.Open Foo.
Print x.
Print x2.

NS.Open A1.
Print B1.c.
Print B1.d.

NS.Open A1.B1.
Print d.

(* boh *)
NS.Begin A2.B2.
Definition e := 1.
NS.End B2.
NS.End A2.
NS.Begin A2.B2.
Definition f := 2.
NS.End A2.B2.
Print A2.B2.f.

NS.Begin X.
Module Y.
Fail NS.Begin Z.
End Y.
NS.End X.