From elpi Require Import elpi.

(**
   This file sketches a procedure to translate a term abstracted over
   a specific record to a term abstracted over the components of that record.

   Example:

     Record r := mk { proj1 : T1; proj2 : T2 }.
     Definition f (x : r) := Body(proj1 x,proj2 x).

   Is expanded to:

     Definition f1 v1 v2 := Body(v1,v2).

   And recursively, if g uses f, then g1 must use f1...

   The idea is to take "f", replace "(x : r)" with as many abstractions as
   needed in order to write "mk v1 v2", then replace "x" with "mk v1 v2", finally
   fire iota reductions such as "proj1 (mk v1 v2) = v1" to obtain "f1".
   
   Then record a global replacement "f x = f1 v2 v2" whenever "x = mk v1 v2".

*)

Elpi Db record.expand.db lp:{{
  % This data base will contain all the expansions performed previously.
  % For example, if f was expandded to f1 we would have this clause:

  % copy (app[f, R | L]) (app[f1, V1, V2 | L1]) :-
  %   copy R (app[k, V1, V2]), std.map L copy L1.

}}.

Elpi Command record.expand.
Elpi Accumulate Db record.expand.db.
Elpi Accumulate lp:{{

% This builds a clause to replace "proji (k y1..yn)" by "yi"
pred build-iotared-clause i:term, i:(pair constant term), o:prop.
build-iotared-clause T   (pr Proj Var)
  (pi L UI AppVar\ copy(app [global (const Proj) UI,T|L]) AppVar :- coq.mk-app Var L AppVar).

% The core algorithm ----------------------------------------------------------

% It is idiomatic in λProlog to perform a single recursion over the data and
% perform multiple tasks while going. Here we both obtain the expanded term
% and the clause that records that expansion. Indeed the binders introduced
% in the new term (standing for the record fialds) and the quantifications
% introduced in the clause are very similar.

% missing in std
pred cons_assoc_opt i:option A, i:B, i:list (pair A B), o:list (pair A B).
cons_assoc_opt none _ X X.
cons_assoc_opt (some A) B X [pr A B|X].

% a package of data that we need to carry but rarely fully access
kind info type.
type info 
    inductive % the record to expand
 -> gref % the term being expanded
 -> gref % the term being expanded and its expanded name
 -> list (option constant) % canonical projections
 -> constructor % record constructor
 -> term % record constructor type
 -> info.

% This predicate turns the OldBo in "fun x : r => OldBo" into
% "fun v1 v2 => NewBo". It is fueled by "KTY" (corresponding to the type
% of the record constructor). In parallel it consumes the list of projections,
% so that it can record that the i-th projection should be replaced by
% the variable standing for the i-th record field (accumulator called Iota)
pred expand-abstraction 
  i:info,
  i:term, % the varibale binding the record in the input term
  
  % fuel
  i:term, % the type of the record constructor
  i:list (option constant), % projections

  i:term, o:term, % the Old and New body
  
  i:term, % constructor applied to all arguments treated so far
  i:list (pair constant term), % iota rules for reductions so far

  % used by expand-spine, accumulated here 
  i:list term, i:list term, % variables for the head of the clause (LHS and RHS)
  i:list prop, o:prop. % accumulator for the premises of the clause, and the clause

expand-abstraction Info Rec (prod N S F) [P|PS] OldBo (fun N S Bo) KArgs Iota AccL AccR Premises (pi x\ Clause x) :-
  pi x\
    expand-abstraction Info Rec
      (F x) PS OldBo (Bo x) {coq.mk-app KArgs [x]} {cons_assoc_opt P x Iota} AccL [x|AccR] Premises (Clause x).

expand-abstraction Info Rec (let N S B F) [P|PS] OldBo (let N S B Bo) KArgs Iota AccL AccR Premises Clause :-
  pi x\ % a let in is not a real argument to KArgs, but may need a "iota" redex, since the projection could exist
    expand-abstraction Info Rec
      (F x) PS OldBo (Bo x) KArgs {cons_assoc_opt P x Iota} AccL AccR Premises Clause.

expand-abstraction Info Rec _ [] OldBo Result  ExpandedRecord Iota AccL AccR Premises Clause :-
  % generate all substitutions
  std.map Iota (build-iotared-clause ExpandedRecord) IotaClauses,
  ExpansionClause = copy Rec ExpandedRecord,
  % eta expand the record to obtain a new body (that typechecks)
  ExpansionClause => copy OldBo NewBo,
  % continue, but schedule iota reductions (pre-existing projections became iota redexes)
  IotaClauses =>
    expand-spine Info NewBo Result AccL AccR [ExpansionClause|Premises] Clause.

% This predicate travrses the spine of lambdas. When it finds an abstraction
% on the record R is calls expand-abstraction. Finally it copies the term,
% applying all substitutions accumulated while descending the spine.
pred expand-spine
  i:info,
  i:term, o:term, % input and output term
  i:list term, i:list term, % variables for the LHS and RHS of the clause head
  i:list prop, o:prop. % premises and final clause

% if we find a lambda over the record R we expand
expand-spine (info R _ _ Projs K KTY as Info) (fun _ (global (indt R) UI) Bo) Result AccL AccR Premises (pi r\ Clause r) :- !,
  pi r\ expand-abstraction Info r KTY Projs (Bo r) Result (global (indc K) UI) [] [r|AccL] AccR Premises (Clause r).

% otherwise we traverse the spine
expand-spine Info (fun Name Ty Bo) (fun Name Ty1 Bo1) AccL AccR Premises (pi x y\ Clause x y) :- !,
  copy Ty Ty1,
  pi x y\ copy x y => expand-spine Info (Bo x) (Bo1 y) [x|AccL] [y|AccR] [copy x y|Premises] (Clause x y).
expand-spine Info (let Name Ty V Bo) (let Name Ty1 V1 Bo1) AccL AccR Premises (pi x y\ Clause x y) :- !,
  copy Ty Ty1,
  copy V V1,
  pi x y\ copy x y => expand-spine Info (Bo x) (Bo1 y) [x|AccL] [y|AccR] [copy x y|Premises] (Clause x y).

% at the end of the spine we fire the iota redexes and complete the clause
expand-spine (info _ GR NGR _ _ _) X Y AccL AccR Premises Clause :-
  copy X Y,
  % we build "app[f,x1..xn|rest]"
  (pi rest1 ui\ coq.mk-app (global GR ui)  {std.append {std.rev AccL} rest1} (L rest1 ui)),
  (pi rest2 ui\ coq.mk-app (global NGR ui) {std.append {std.rev AccR} rest2} (R rest2 ui)),
  % we can now build the clause "copy (app[f,L1..Ln|Rest1]) (app[f1,R1..Rn|Rest2])"
  % here we quantify only the tails, the other variables were quantified during
  % expand-*
  Clause = (pi rest1 rest2 ui\ copy (L rest1 ui) (R rest2 ui) :- [!, std.map rest1 copy rest2 | Premises]).

% The entry point of the main algorithm, just fetchs some data and passes initial
% values for the accumulators.
pred expand i:inductive, i:gref, i:gref, i:term, o:term, o:prop.
expand R GR NGR X Y Clause :-
  std.assert! (coq.env.indt R _ tt 0 0 _ [K] [KTY]) "record is too complex for this example",
  coq.CS.canonical-projections R Projs,
  expand-spine (info R GR NGR Projs K KTY) X Y [] [] [] Clause.

% This simply dispatches between global references ----------------------------

% The only cleverness is that "expand" also builds the clause to be added to
% the data base, and that clause has to mention the name of the constant to be
% generated. Since we don't know it yet (Coq tells us in response to coq.env.add-const)
% we postulate a name for that constant "nc" and later replace it with the real one "NC"
pred expand-gref i:inductive, i:gref, i:string, o:prop.
expand-gref Record (const C) Name Clause :- !,
  std.assert! (coq.env.const C _ (some Bo) _) "only transparent constants can be expanded",
  (pi nc\ expand Record (const C) nc Bo NewBo (NClause nc)),
  std.assert-ok! (coq.typecheck NewBo _) "illtyped",
  coq.env.add-const Name NewBo _ _ NC,
  Clause = NClause (const NC).

expand-gref _ (indt _) _ _ :- coq.error "Not implemented yet".

expand-gref _ (indc _) _ _ :- coq.error "It makes no sense to expand a constructor alone, expand the inductive instead".

% Entry point -----------------------------------------------------------------
main [str R, str In, str Prefix] :- !,
  std.assert! (coq.locate R (indt Record)) "The first argument must be a record name",
  std.assert! (coq.locate In GR) "The second argument must be a global term",
  NewName is Prefix ^ {coq.gref->id GR},

  expand-gref Record GR NewName Clause,

  % We want our clauses to take precensence over the structural ones of "copy"
  coq.elpi.accumulate _ "record.expand.db" (clause _ (before "copy:start") Clause).

main _ :- coq.error "usage: Elpi record.expand record_name global_term prefix".
}}.
Elpi Typecheck.

Record r := { T :> Type; X := T; op : T -> X -> bool }.

Definition f b (t : r) (q := negb b) := fix rec (l1 l2 : list t) :=
  match l1, l2 with
  | nil, nil => b
  | cons x xs, cons y ys => andb (op _ x y) (rec xs ys)
  | _, _ => q
  end.

Elpi record.expand r f "expanded_".
Print f.
Print expanded_f.

(* so that we can see the new "copy" clause *)
Elpi Print record.expand.

Definition g t l s h := (forall x y, op t x y = false) /\ f true t l s = h.

Elpi record.expand r g "expanded_".
Print expanded_g.
