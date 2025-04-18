From elpi Require Import elpi.

Elpi Command test.API.

Elpi Query lp:{{
  coq.version V MA MI P,
  std.assert! (MA = 8 ; MA = 9) "Coq major version not 8 or 9",
  std.assert! (MI >= 0 ; MI < 20) "Coq minor version not in 0 - 20",
  % std.assert! (P >= 0 ; P > -5) "Coq never made so many betas",
  coq.say "Coq version:" V "=" MA "." MI "." P.
}}.

Elpi Command version.
Elpi Accumulate lp:{{

% elpi:if version rocq-elpi < 2.0.0
main _ :- coq.error "bad".
% elpi:endif

main _ :- true.

}}.
Elpi version.

(****** say *************************************)

Elpi Query lp:{{
  coq.say "hello world"
}}.

(****** warnings *************************************)

Set Warnings "-elpi,-category,+unknown-warning".
Elpi Query lp:{{
  coq.warn "this is a generic warning".
}}.

Elpi Query lp:{{
  coq.say "A",
  coq.warning "category" "name"  "this is a warning with a name an category".
}} lp:{{
  coq.say "B",
  coq.warning "category" "name"  "this is a warning with a name an category".
}}.

Set Warnings "+category".

Elpi Query lp:{{
  coq.warning "category" "name"  "this is a warning with a name an category".
}} lp:{{ coq.warning "category" "name"  "this is a warning with a name an category". }}.
Fail Elpi Query lp:{{
  coq.warning "category" "name"  "this is another  warning with a name an category".
}} lp:{{ coq.warning "category" "name"  "this is a warning with a name an category". }}.
Set Warnings "elpi,category".

(****** locate **********************************)

(* nametab *)
Elpi Query lp:{{
  coq.locate "nat"                    (indt GR),
  coq.locate "Datatypes.nat"          (indt GR),
  coq.locate "Init.Datatypes.nat"     (indt GR),
  coq.locate "Coq.Init.Datatypes.nat" (indt GR).
}}.

Fail Elpi Query lp:{{
  coq.locate "foobar" _.
}}.

Elpi Query lp:{{
  coq.locate "plus"    (const GR),
  coq.locate "Nat.add" (const GR),
  coq.locate-module "Init.Datatypes" MP_.
}}.

Notation succ x := (S x).

Elpi Query lp:{{ std.do! [
  coq.locate-all "plus"    X1, X1 = [loc-gref (const GR)],
  coq.locate-all "Nat.add" X2, X2 = [loc-gref (const GR)],
  coq.locate-all "succ"    X3, X3 = [loc-abbreviation A_],
  coq.locate-all "Init.Datatypes" X4, X4 = [loc-modpath MP_],
  coq.locate-all "fdsfdsjkfdksljflkdsjlkfdjkls" [],
].
}}.


(***** Univs *******************************)

Elpi Query lp:{{coq.univ.print}}.
Elpi Query lp:{{coq.univ.new X_}}.
Elpi Query lp:{{coq.sort.leq X_ Y_}}.
Elpi Query lp:{{coq.sort.eq X_ Y_}}.
Elpi Query lp:{{coq.sort.pts-triple X_ Y_ Z_}}.
Elpi Query lp:{{coq.sort.sup X_ Y_}}.


(********* accumulate *************** *)
 
Elpi Db test.db lp:{{type foo string -> prop.}}.
Elpi Command test.use.db.
Elpi Accumulate Db test.db.
#[synterp] Elpi Accumulate lp:{{
  main [] :- coq.env.begin-module "test_db_accumulate" none, coq.env.end-module _.
}}.
Elpi Accumulate lp:{{
  main [] :-
    coq.elpi.accumulate _ "test.db"
      (clause _ _ (pi x\ foo x :- x = "here")),
    coq.env.begin-module "test_db_accumulate" _,
    coq.elpi.accumulate current "test.db"
      (clause _ _ (pi x\ foo x :- x = "there")),
    coq.env.end-module _.
}}.


Fail Elpi Query lp:{{foo _}}.
Elpi test.use.db.
Elpi Query lp:{{foo "here"}}.

Fail Elpi Query lp:{{foo "there"}}.
Import test_db_accumulate.
Elpi Query lp:{{foo "there"}}.
Module xx := test_db_accumulate.


Elpi Db test2.db lp:{{
    type foo gref -> prop.
}}.
Elpi Command test2.use.db.
Elpi Accumulate Db test2.db.
Elpi Accumulate lp:{{
  main [str S] :- coq.locate S GR, coq.elpi.accumulate _ "test2.db" (clause _ _ (foo GR)).
  main [str "local", str S] :- coq.locate S GR, @local! => coq.elpi.accumulate _ "test2.db" (clause _ _ (foo GR)).
  main [int N] :- std.findall (foo X_) L, coq.say L, std.length L N.
}}.

Module T2.
Section T2.
Variable X : nat.
Elpi test2.use.db X.
Elpi test2.use.db nat.
Elpi test2.use.db "local" bool.
Elpi test2.use.db 3.
End T2.
Elpi test2.use.db "local" bool.
Elpi test2.use.db 2.
End T2.
Elpi test2.use.db 0.
Import T2.
Elpi test2.use.db 1.


Section T3. Fail Elpi Db test3.db lp:{{ }}. End T3.
Module T3. Fail Elpi Db test3.db lp:{{ }}. End T3.

(* scope grafted clauses, again and across files *)

Elpi Db global.db lp:{{
  pred declared o:string.

  :name "init"
  declared _ :- fail.
}}.
Elpi Command declare.
Elpi Accumulate Db global.db.
#[synterp] Elpi Accumulate lp:{{
main [str "library",_] :- coq.env.begin-module "ClausesL" none, coq.env.end-module _.
main [str "current",_] :- coq.env.begin-module "ClausesC" none, coq.env.end-module _.
main [str "execution-site",_] :- coq.env.begin-module "ClausesE" none, coq.env.end-module _.
}}.
Elpi Accumulate lp:{{

main [str "library", str I] :-
  coq.env.begin-module "ClausesL" _,
  coq.elpi.accumulate library "global.db" (clause _ (before "init") (declared I)),
  coq.env.end-module _.
main [str "current", str I] :-
  coq.env.begin-module "ClausesC" _,
  coq.elpi.accumulate current "global.db" (clause _ (before "init") (declared I)),
  coq.env.end-module _.
main [str "execution-site", str I] :-
  coq.env.begin-module "ClausesE" _,
  coq.elpi.accumulate execution-site "global.db" (clause _ (before "init") (declared I)),
  coq.env.end-module _.

}}.


Elpi Command declare.test.
Elpi Accumulate Db global.db.
Elpi Accumulate lp:{{

main [str "mem", str I] :-
  std.assert! (declared I) "clause not present".
main [str "length", int I] :-
  std.findall (declared J_) L,
  std.assert! (std.length L I) "wrong number of clauses".

}}.



Module Box.
Elpi declare "current" "BOX.ClausesC".
Fail Elpi declare.test "mem" "BOX.ClausesC".

Elpi declare "library" "GLOBAL".
Elpi declare "execution-site" "BOX".
Elpi declare.test "mem" "GLOBAL".
Elpi declare.test "mem" "BOX".
Elpi declare.test "length" 2.

End Box.

Elpi declare.test "mem" "GLOBAL".
Fail Elpi declare.test "mem" "BOX".
Elpi declare.test "length" 1.

Export Box.
Elpi declare.test "mem" "BOX".
Elpi declare.test "length" 2.

Import Box.ClausesC.
Elpi declare.test "mem" "BOX.ClausesC".
Elpi declare.test "length" 3.

(********* options ************)

Elpi Query lp:{{ % see test_API.v
  
  coq.option.add ["Foo", "Bar"] (coq.option.string (some "x")) tt

}}.


(********* export *************** *)

Elpi Command export.me.
Elpi Accumulate lp:{{ main A :- coq.say "hello" A. }}.


Elpi Export export.me.

export.me 1 2 (nat) "x".

(************* halt ********************)

Elpi Command halt.
Elpi Accumulate lp:{{
  main _ :- std.assert! (3 = 2) "ooops".
}}.
Fail Elpi halt.

(**********************************************)

Elpi Command test.pp.
Elpi Accumulate lp:{{
main _ :- std.do! [
  P = coq.pp.box (coq.pp.hv 2) [coq.pp.str "Module", coq.pp.spc, coq.pp.str "Foo", coq.pp.spc, coq.pp.str":=", coq.pp.brk 1 0, coq.pp.str "body", coq.pp.spc, coq.pp.str "End Foo."],
  coq.say P,
  @ppwidth! 15 => coq.say {coq.pp->string P},
  @ppall! => coq.say {coq.term->string {{ fix foo x y {struct x} := match x in bool with false => y | true => 3 end }} },
  @ppmost! => coq.say {coq.term->string {{ fix foo x y {struct x} := match x in bool with false => y | true => 3 end }} },
].
}}.
Elpi test.pp.

