From elpi Require Import elpi.
Set Allow StrictProp.
Inductive foo : SProp := K : nat -> foo.
Set Printing Relevance Marks.
Definition f (x : foo) := x.

Elpi Command test.
Elpi Query lp:{{
  const F = {{:gref f}},
  coq.env.const F (some (fun N _ _)) Ty,
  std.assert!(coq.name.relevant? N (some ff))"bad relevance"

}}.

Elpi Query lp:{{
  B = fun N {{ nat }} (x\x),
  coq.say {coq.term->string B},
  std.assert!(coq.name.relevant? N none)"bad relevance",
  coq.env.add-const "xxx" B _ tt _


}}.
Print xxx.

Elpi Query lp:{{
  B = fun N {{ nat }} (x\{{ K lp:x }}),
  coq.typecheck B _ ok,
  std.assert!(coq.name.relevant? N (some tt))"bad relevance",
  coq.say {coq.term->string B}

}}.

Elpi Query lp:{{
  B = fun N {{ foo }} (x\x),
  coq.typecheck B _ ok,
  std.assert!(coq.name.relevant? N (some ff))"bad relevance",
  coq.say {coq.term->string B}

}}.

(* Check fun x : nat => K x.
Check fun x : foo => x. *)