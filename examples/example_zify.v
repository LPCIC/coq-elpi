From elpi Require Import elpi.
From Coq Require Import ssreflect.

Elpi Db zify.db lp:{{

% The identity substitution, to be patched later on by the user
pred zify i:term, o:term.
:name "zify:start"
zify X X :- name X.
zify (global _ as C) C :- !.
zify (sort _ as C) C :- !.
zify (fun N T F) (fun N T1 F1) :- !,
  zify T T1, @pi-decl N T x\ zify x x => zify (F x) (F1 x).
zify (let N T B F) (let N T1 B1 F1) :- !,
  zify T T1, zify B B1, @pi-def N T B x\ zify x x => zify (F x) (F1 x).
zify (prod N T F) (prod N T1 F1) :- !,
  zify T T1, @pi-decl N T x\ zify x x => zify (F x) (F1 x).
zify (app L) (app L1) :- !, std.map L zify L1.
zify (fix N Rno Ty F) (fix N Rno Ty1 F1) :- !,
  zify Ty Ty1, @pi-decl N Ty x\ zify x x => zify (F x) (F1 x).
zify (match T Rty B) (match T1 Rty1 B1) :- !,
  zify T T1, zify Rty Rty1, std.map B zify B1.
zify (primitive _ as C) C :- !.

% The identity contraction, to be patched later on by the user
pred contract i:term, o:term.
:name "contract:start"
contract X X :- name X.
contract (global _ as C) C :- !.
contract (sort _ as C) C :- !.
contract (fun N T F) (fun N T1 F1) :- !,
  contract T T1, @pi-decl N T x\ contract x x => contract (F x) (F1 x).
contract (let N T B F) (let N T1 B1 F1) :- !,
  contract T T1, contract B B1, @pi-def N T B x\ contract x x => contract (F x) (F1 x).
contract (prod N T F) (prod N T1 F1) :- !,
  contract T T1, @pi-decl N T x\ contract x x => contract (F x) (F1 x).
contract (app L) (app L1) :- !, std.map L contract L1.
contract (fix N Rno Ty F) (fix N Rno Ty1 F1) :- !,
  contract Ty Ty1, @pi-decl N Ty x\ contract x x => contract (F x) (F1 x).
contract (match T Rty B) (match T1 Rty1 B1) :- !,
  contract T T1, contract Rty Rty1, std.map B contract B1.
contract (primitive _ as C) C :- !.

}}.

Ltac my_suffices x := suff: x.

Elpi Tactic zify.
Elpi Accumulate Db zify.db.
Elpi Accumulate lp:{{

solve _ [G] GLS :- std.do! [
  G = goal Ctx _ Ty _,
  Ctx => std.do! [
    zify Ty Ty1,
    std.assert-ok! (coq.typecheck Ty1 _) "zify has a bug",
    contract Ty1 Ty2,
    std.assert-ok! (coq.typecheck Ty2 _) "contract has a bug",
    coq.ltac1.call "my_suffices" [Ty2] G GLS,
  ],
].

}}.
Elpi Typecheck.

Axiom Z : Type.
Axiom n2z : nat -> Z.
Axiom z2n : Z -> nat.
Axiom zadd : Z -> Z -> Z.
Axiom z1 : Z.

(* We add rules to the contract procedure for Z *)

Elpi Accumulate zify.db lp:{{

  :before "contract:start"
  contract {{ @eq nat (z2n lp:A) (z2n lp:B) }} {{ @eq Z lp:A1 lp:B1 }} :-
    contract A A1, contract B B1.

  :before "contract:start"
  contract {{ (z2n (n2z lp:A)) }} {{ lp:A1 }} :- contract A A1.

  :before "contract:start"
  contract {{ (n2z (z2n lp:A)) }} {{ lp:A1 }} :- contract A A1.

}}.

(* We add a rule for S *)

Elpi Accumulate zify.db lp:{{

  :before "zify:start"
  zify {{ S lp:X }} {{ z2n (zadd z1 (n2z lp:X1)) }} :- zify X X1.

}}.

Lemma example x y : y + S (S x) = x.
Proof.
    elpi zify.
    (* y + z2n (zadd z1 (zadd z1 (n2z x))) = x *)
Abort.

(* We add a rule for + *)

Elpi Accumulate zify.db lp:{{

  :before "zify:start"
  zify {{ lp:X + lp:Y }} {{ z2n (zadd (n2z lp:X1) (n2z lp:Y1)) }} :- zify X X1, zify Y Y1.

}}.

Lemma example x y : y + S (S x) = x.
Proof.
    elpi zify.
    (* z2n (zadd (n2z y) (zadd z1 (zadd z1 (n2z x)))) = x *)
Abort.
