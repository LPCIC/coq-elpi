From elpi Require Import elpi. 

Elpi Program tutorial lp:{{

  kind person  type.
  type mallory, bob, alice  person.

}}.

Elpi Accumulate lp:{{
  pred last i:list A, o:A.
  last [] _ :- fatal-error "last on empty list".
  last [X] X :- !.
  last [_|XS] R :- last XS R.

  my_last RES [A | L] :- my_last RES L, !.
  my_last RES [RES].

  my_last_but_one RES [RES, _] :- !.
  my_last_but_one RES [A | L] :- my_last_but_one RES L, !.
}}.

Elpi Query lp:{{
  L = [1, 2, 4, 5, 7, 55, 1, 2, 35],
  my_last LAST L, my_last_but_one BEF_LAST L, last L RES1, coq.say "ciao".
}}.

Elpi Accumulate lp:{{
  element_at A [A | _] 1.
  element_at RES [_ | L] N :- N > 1, M is N - 1, element_at RES L M.

  list_len 0 [].
  list_len RES [_ | L] :- list_len M L, RES is M + 1.
}}.

(* Elpi Accumulate lp:{{
  L = [100, 2, 4, 5, 7, 55, 1, 2, 35]. *)
(* }}. *)

Elpi Query lp:{{
  L = [100, 2, 4, 5, 7, 55, 1, 2, 35],
  element_at RES L 5, list_len LEN L.
}}.

Elpi Accumulate lp:{{
  reverse_aux [] A A :- !.
  reverse_aux [A | L] RES ACC :- reverse_aux L RES [A | ACC].

  reverse L RES :- reverse_aux L RES [].
}}.

Elpi Query lp:{{
  L = [100, 2, 4, 5, 7, 55, 1, 2, 35],
  reverse RES L.
}}.

Elpi Accumulate lp:{{
  % same [] [] :- true.
  % same [A | L1] [A | L2] :- same L1 L2.

  % palindrome L :- reverse L RES, same RES L.  
  palindrome L :- reverse L L.  

  % HELP HERE: in prolog it should continue de search ?
  % Should I put the bang on line 64 ?

  compress [] [].
  compress [X] [X].
  compress [X,X|Xs] Zs :- compress [X|Xs] Zs.
  compress [X,Y|Ys] [X|Zs] :- compress [Y|Ys] Zs.
}}.


Elpi Query lp:{{
  L = [1, 2, 3, 2, 1],
  palindrome L, compress [1,1,1,1,2,3,3,3,3,2,2,2,1,2,2,2] RES.
}}.

Elpi Accumulate lp:{{
  pack_aux [] [] [] [].
  pack_aux [A] [[A]] [] [].
  pack_aux [] [ACC | H] H ACC.
  pack_aux [A | L] RES H [A | ACC] :- pack_aux L RES H [A, A | ACC], !.
  pack_aux [A | L] RES H [B | ACC] :- pack_aux L RES [[B | ACC] | H] [A].
  pack_aux [A | L] RES H [] :- pack_aux L RES H [A].

  pack L RES :- pack_aux L RES [] [].
}}.

Elpi Query lp:{{
  L = [1, 1, 35, 7,7],
  pack L RES.
}}.

Elpi Trace Browser.
Elpi Query lp:{{
  L1 = [1,2,3],
  L2 = [4,5,6],
  L3 = [1,2,3,4,5,6],
  std.append L1 RES L3, std.take 4 L3 ELT, 5 < 7.
}}.

Definition f := fun x : nat => x.

Elpi Query lp:{{

  coq.locate "f" (const C),
  coq.env.const C (some Bo) _

}}.

Definition x := 2.

Elpi Query lp:{{

  coq.locate "x" GR,

  % all global references have a type
  coq.env.typeof GR Ty,

  % destruct GR to obtain its constant part C
  GR = const C,

  % constants may have a body, do have a type
  coq.env.const C (some Bo) TyC

}}.

Elpi Query lp:{{

  coq.locate "plus" (const C),
  coq.env.const C (some Bo) _

}}.

Elpi Query lp:{{

  X = (x\y\ {{ lp:y + lp:x }}), % x and y live in Elpi
  F = {{ fun a b : nat => lp:(X a b) }},

  coq.say F  % a and b live in Coq

}}.

Elpi Query lp:{{
  fun `foo` T (x\x) = fun `bar` T (x\x)
}}.

Elpi Query lp:{{

  coq.locate "plus" (const C),
  coq.env.const C (some Bo) _

}}.

Elpi Tactic blind.
Elpi Accumulate lp:{{
  solve (goal _ Trigger _ _ _) [] :- Trigger = {{0}}.
  solve (goal _ Trigger _ _ _) [] :- Trigger = {{I}}.
}}.

Lemma test_blind : True * nat.
split.
elpi blind.
elpi blind.
Show Proof.
Qed.

Elpi Tactic blind_bad.
Elpi Accumulate lp:{{
  solve (goal _ _ _ Proof _) [] :- Proof = {{0}}.
  solve (goal _ _ _ Proof _) [] :- Proof = {{I}}.
}}.

Lemma test_blind1 : True * nat.
split.
elpi blind_bad.
elpi blind_bad.
Show Proof.
Abort.

About conj.
Elpi Tactic split1.
Elpi Accumulate lp:{{
  solve (goal A B ({{_ /\ _}} as F) D E as G) GL :- !,
    coq.say "A: " A,
    coq.say "B: " B,
    coq.say "C: " C,
    coq.say "D: " D,
    coq.say "E: " E,
    coq.sigma.print,
   refine {{conj _ _ }} G GL
   .

  solve _ _ :- coq.ltac.fail _ "not a conjunction".
}}.

Lemma test_split : exists t : Prop, True /\ True /\ t.
Proof.
  eexists.
  repeat elpi split1.
  all: elpi blind.
Qed.

Lemma xx (A : Type) (r g : A -> A) (a b : A): (forall x, r x = g x) -> g a = g b -> r a = g b.
Proof.
  intros Hfg t.
  refine (eq_trans (Hfg _) t).
Qed.

Parameters A B C : Prop.

Theorem t1:
  A -> B -> C.
Admitted.

Theorem t2:
  A -> B <-> C.
Admitted.

Theorem test1:
  A -> B -> C.
Proof.
  intros.
  refine (t1 _ _).
  assumption.
  assumption.
Qed.

Theorem test2:
  A -> B -> C.
Proof.
  intros.
  refine (proj1 (t2 _) _).
  all:assumption.
Qed.


(* 
  fix plus' 0 :=
     fun n m => match n with O => m | S p => S (plus' p m) end
 *)
  