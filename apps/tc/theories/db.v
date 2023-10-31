(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

From elpi Require Import elpi.
Elpi Db tc.db lp:{{
  % the type of search for a typeclass
  % deterministic :- no backtrack after having found a solution/fail
  % classic       :- the classic search, if a path is failing, we backtrack
  kind search-mode type.
  type deterministic  search-mode.
  type classic        search-mode.

  % contains the instances added to the DB 
  % associated to the list of sections they belong to
  pred instance o:list string, o:gref, o:gref.

  % contains the typeclasses added to the DB
  pred classes o:gref, o:search-mode.

  % pred on which we graft instances in the database
  pred hook o:string.
  :name "firstHook" hook "firstHook".
  :name "lastHook" hook "lastHook".

  % the set of instances that we are not yet able to compile, 
  % in majority they use universe polimorphism
  pred banned o:gref.

  % [tc-signature TC Modes], returns for each Typeclass TC
  % its Modes
  pred tc-mode i:gref, o:list (pair argument_mode string).
}}.