(**
   This file mocks up a reduction tactic unfolding only constants
   from a given module.
*)

From elpi Require Import elpi.

Elpi Tactic reduce.
Elpi Accumulate lp:{{

pred gref->redflag i:gref, o:coq.redflag.
gref->redflag (const C) (coq.redflags.const C).

solve (goal _ _ Ty _ [str M] as G) GS :-
  coq.locate-module M MP,
  coq.env.module MP GREFS,
  std.filter GREFS (x\x = const _) CONSTANTS,
  std.map CONSTANTS (gr\r\ coq.env.transitive-dependencies gr _ r) DEPS,
  std.fold DEPS {coq.gref.set.empty} coq.gref.set.union ALLDEPS,
  std.append CONSTANTS {coq.gref.set.elements ALLDEPS} All,
  std.map-filter All gref->redflag DELTAFLAGS,
  coq.redflags.add coq.redflags.nored
    [ coq.redflags.beta, coq.redflags.fix, coq.redflags.match | DELTAFLAGS ]
    F,
  @redflags! F => coq.reduction.cbv.norm Ty Ty1,
  refine {{ _ : lp:Ty1 }} G GS. % to leave a vmcast one needs to call ltac1

}}.
Elpi Typecheck.


Module ToRed.
Definition x := 1.
Definition y := 1.
Definition alias := plus.
End ToRed.

Goal ToRed.x + ToRed.y = let z := 1 in S z.
elpi reduce "ToRed".
match goal with |- 2 = let z := 1 in S z => trivial end.
Show Proof.
Abort.
