(* Automatically generated from elpi/coq-HOAS.elpi, don't edit *)
let code = {|
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% coq-HOAS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% This section contains the low level data types linking Coq and elpi.
% In particular:
%   - the data type for terms and the evar_map entries (a sequent)
%   - the entry points for commands and tactics (main and solve)

% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Entry points
%
% Command and tactic invocation
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Entry point for commands. Eg. "#[att=true] Elpi mycommand foo 3 (f x)." becomes
%   main [str "foo", int 3, trm (app[f,x])]
% in a context where
%   attributes [attribute "att" (leaf "true")]
% holds. The encoding of terms is described below.
% See also the coq.parse-attributes utility.
pred main i:list argument.
pred usage.
pred attributes o:list attribute.

% Entry point for tactics. Eg. "elpi mytactic foo 3 (f x)." becomes
%   solve <goal> <new goals>
% Where [str "foo", int 3, trm (app[f,x])] is part of <goal>.
% The encoding of goals is described below.
pred solve i:goal, o:list sealed-goal.

% The data type of arguments (for commands or tactics)
kind argument type.
type int       int    -> argument. % Eg. 1 -2.
type str       string -> argument. % Eg. x "y" z.w. or any Coq keyword/symbol
type trm       term   -> argument. % Eg. (t).

% Extra arguments for commands. [Definition], [Axiom], [Record] and [Context]
% take precedence over the [str] argument above (when not "quoted").
%
% Eg. Record m A : T := K { f : t; .. }.
type indt-decl indt-decl -> argument.
% Eg. Definition m A : T := B. (or Axiom when the body is none)
type const-decl id -> option term -> arity -> argument.
% Eg. Context A (b : A).
type ctx-decl context-decl -> argument.

% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Coq's terms
%
% Types of term formers
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% -- terms --------------------------------------------------------------------
kind term type.

type sort  universe -> term. % Prop, Type@{i}

% constants: inductive types, inductive constructors, definitions
type global gref -> term.

% binders: to form functions, arities and local definitions
type fun  name -> term -> (term -> term) -> term.         % fun x : t =>
type prod name -> term -> (term -> term) -> term.         % forall x : t,
type let  name -> term -> term -> (term -> term) -> term. % let x : T := v in

% other term formers: function application, pattern matching and recursion
type app   list term -> term.                   % app [hd|args]
type match term -> term -> list term -> term.   % match t p [branch])
type fix   name -> int -> term -> (term -> term) -> term. % fix name rno ty bo

kind primitive-value type.
type uint63 uint63 -> primitive-value.
type float64 float64 -> primitive-value.
type primitive primitive-value -> term.


% NYI
%type cofix name -> term -> (term -> term) -> term. % cofix name ty bo
%type proj  @gref -> term -> term. % applied primitive projection

% Notes about (match Scrutinee TypingFunction Branches) when
%   Inductive i A : A -> nat -> Type := K : forall a : A, i A a 0
% and
%   Scrutinee be a term of type (i bool true 7)
%
% - TypingFunction has a very rigid shape that depends on i. Namely
%   as many lambdas as indexes plus one lambda for the inductive itself
%   where the value of the parameters are taken from the type of the scrutinee:
%     fun `a` (indt "bool") a\
%      fun `n` (indt "nat) n\
%       fun `i` (app[indt "i", indt "bool", a n) i\ ..
%   Such spine of fun cannot be omitted; else elpi cannot read the term back.
%   See also coq.bind-ind-arity in coq-lib.elpi, that builds such spine for you,
%   or the higher level api coq.build-match (same file) that also takes
%   care of breanches.
% - Branches is a list of terms, the order is the canonical one (the order
%   of the constructors as they were declared). If the constructor has arguments
%   (excluding the parameters) then the corresponding term shall be a Coq
%   function. In this case
%      fun `x` (indt "bool") x\ ..

% -- helpers ------------------------------------------------------------------
macro @cast T TY :- (let `cast` TY T x\x).

% -- misc ---------------------------------------------------------------------

% When one writes Constraint Handling Rules unification variables are "frozen",
% i.e. represented by a fresh constant (the evar key) and a list of terms
% (typically the variables in scope).
kind evarkey type.
type uvar  evarkey -> list term -> term.


% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Coq's evar_map
%
% Context and evar declaration
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% An evar_info (displayed as a Coq goal) is essentially a sequent:
%
% x : t
% y := v : x
% ----------
% p x y
%
% is coded as an Elpi query
%
% pi x1\ decl x1 `x` <t> =>
%  pi x2\ def x2 `y` x1 <v> =>
%   declare-evar
%      [decl x1 `x` <t>, def x2 `y` x1 <v>]
%      (RawEvar x1 x2) (<p> x1 x2) (Ev x1 x2)
%
% where, by default, declare-evar creates a syntactic constraint as
%
% {x1 x2} :
%   decl x1 `x` <t>, def x2 `y` x1 <v> ?-
%     evar (RawEvar x1 x2) (<p> x1 x2) (Ev x1 x2)  /* suspended on RawEvar, Ev */
%
% When the program is over, a remaining syntactic constraint like the one above
% is read back and transformed into the corresponding evar_info.

pred decl i:term, o:name, o:term. % Var Name Ty
pred def  i:term, o:name, o:term, o:term. % Var Name Ty Bo
pred declare-evar i:list prop, i:term, i:term, i:term. % Ctx RawEvar Ty Evar

:name "default-declare-evar"
declare-evar Ctx RawEv Ty Ev :-
  declare_constraint (declare-evar Ctx RawEv Ty Ev) [RawEv].

% When a goal (evar _ _ _) is turned into a constraint the context is filtered
% to only contain decl, def, pp.  For now no handling rules for this set of
% constraints other than one to remove a constraint

pred rm-evar i:term, i:term.
rm-evar (uvar as X) (uvar as Y):- !, declare_constraint (rm-evar X Y) [X,Y].
rm-evar _ _.

constraint declare-evar evar def decl cache rm-evar {

   % Override the actual context
   rule \ (declare-evar Ctx RawEv Ty Ev) <=> (Ctx => evar RawEv Ty Ev).

   rule \ (rm-evar (uvar X _) (uvar Y _)) (evar (uvar X _) _ (uvar Y _)).

}

% The (evar R Ty E) predicate suspends when R and E are flexible,
% and is solved otherwise.
% The client may want to provide an alternative implementation of
% the clause "default-assign-evar", for example to typechecks that the
% term assigned to E has type Ty, or that the term assigned to R
% elaborates to a term of type Ty that gets assigned to E.
% In tactic mode, elpi/coq-elaborator.elpi wires things up that way.

pred evar i:term, i:term, o:term. % Evar Ty RefinedSolution
evar (uvar as X) T S :- !,
  if (var S) (declare_constraint (evar X T S) [X, S])
             true. % If S is assigned we consider its a well type term

:name "default-assign-evar"
evar _ _ _. % volatile, only unresolved evars are considered as evars

% To ease the creation of a context with decl and def
% Eg.  @pi-decl `x` <t> x1\ @pi-def `y` <t> <v> y\ ...
macro @pi-decl N T F :- pi x\ decl x N T => F x.
macro @pi-def N T B F :- pi x\ def x N T B => cache x B_ => F x.
macro @pi-parameter ID T F :-
  sigma N\ (coq.id->name ID N, pi x\ decl x N T => F x).
macro @pi-inductive ID A F :-
  sigma N\ (coq.id->name ID N, coq.arity->term A T, pi x\ decl x N T => F x).

% Sometimes it can be useful to pass to Coq a term with unification variables
% representing "untyped holes" like an implicit argument _. In particular
% a unification variable may exit the so called pattern fragment (applied
% to distinct variables) and hence cannot be reliably mapped to Coq as an evar,
% but can still be considered as an implicit argument.
% By loading in the context get-option "HOAS:holes" tt one forces that
% behavior. Here a convenience macro to be put on the LHS of =>
macro @holes! :- get-option "HOAS:holes" tt.

% Similarly, some APIs take a term skeleton in input. In that case unification
% variables are totally disregarded (not even mapped to Coq evars). They are
% interpreted as the {{ lib:elpi.hole }} constant, which represents an implicit
% argument. As a consenque these APIs don't modify the input term at all, but
% rather return a copy. Note that if {{ lib:elpi.hole }} is used directly, then
% it has to be applied to all variables in scope, since Coq erases variables
% that are not used. For example using {{ forall x : nat, lib:elpi.hole }} as
% a term skeleton is equivalent to {{ nat -> lib:elpi.hole }}, while
% {{ forall x : nat, lib:elpi.hole x lib:elpi.hole more args }} puts x in
% the scope of the hole (and passes to is more args).

% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Coq's goals and tactic invocation
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% A Coq goal is essentially a sequent, like the evar_info above, but since it
% has to be manipulated as first class Elpi data, it is represented in a slightly
% different way. For example
%
% x : t
% y := v : x
% ----------
% g x y
%
% is represented by the following term of type sealed-goal
%
%  nabla x1\
%   nabla x2\
%    seal
%      (goal
%         [decl x1 `x` <t>, def x2 `y` x1 <v>]
%         (RawEvar x1 x2) (<g> x1 x2) (Evar x1 x2)
%         (Arguments x1 x2))

kind goal type.
kind sealed-goal type.
type nabla (term -> sealed-goal) -> sealed-goal.
type seal goal -> sealed-goal.

typeabbrev goal-ctx (list prop).
type goal goal-ctx -> term -> term -> term -> list argument -> goal.

% A sealed-goal closes with nabla the bound names of a
% 
%  (goal Ctx RawSolution Ty Solution Arguments)
%
% where Ctx is a list of decl or def and Solution is a unification variable
% to be assigned to a term of type Ty in order to make progress.
% RawSolution is used as a trigger: when a term is assigned to it, it is
% elaborated against Ty and the resulting term is assigned to Solution.
%
% Arguments contains data attached to the goal, which lives in its context
% and can be used by tactics to solve the goals.

% A tactic (an elpi predicate which makes progress on a Coq goal) is
% a predicate of type
%   sealed-goal -> list sealed-goal -> prop
% 
% while the main entry point for a tactic written in Elpi is solve
% which has type
%    goal -> list sealed-goal -> prop
%
% The utility (coq.ltac.open T G GL) postulates all the variables bounds
% by nabla and loads the goal context before calling T on the unsealed
% goal. The invocation of a tactic with arguments
%   3 x "y" (h x)
% on the previous goal results in the following Elpi query:
%
% (pi x1\ decl x1 `x` <t> =>
%   pi x2\ def x2 `y` x1 <v> =>
%    declare-evar
%       [decl x1 `x` <t>, def x2 `y` x1 <v>]
%       (RawEvar x1 x2) (<g> x1 x2) (Evar x1 x2)),
% (coq.ltac.open solve
%  (nabla x1\ nabla x2\ seal
%   (goal
%     [decl x1 `x` <t>, def x2 `y` x1 <v>]
%     (RawEvar x1 x2) (<g> x1 x2) (Evar x1 x2)
%     [int 3, str `x`, str`y`, trm (app[const `h`,x1])]))
%   NewGoals)
%
% If the goal sequent contains other evars, then a tactic invocation is
% an Elpi query made of the conjunction of all the declare-evar queries
% corresponding to these evars and the query corresponding to the goal
% sequent. NewGoals can be assigned to a list of goals that should be
% declared as open. Omitted goals are shelved. If NewGoals is not
% assigned, then all unresolved evars become new goals, but the order
% of such goals is not specified.

% The file elpi-ltac.elpi provides a few combinators (other than coq.ltac.open)
% in the tradition of LCF tacticals. The main difference is that the arguments
% of custom written tactics must not be passed as predicate arguments but rather
% put in the goal they receive. Indeed these arguments can contain terms, and
% their bound variables cannot escape the seal. coq.ltac.set-goal-arguments
% can be used to put an argument from the current goal context into another
% goal. The coq.ltac.call utility can call Ltac1 code (written in Coq) and
% pass arguments via this mechanism.

% Last, since Elpi is alerady a logic programming language with primitive
% support for unification variables, most of the work of a tactic can be
% performed without using tacticals (which work on sealed goals) but rather
% in the context of the original goal. The last step is typically to call
% the refine utility with a term synthesized by the tactic or invoke some
% Ltac1 code on that term (e.g. to call vm_compute, see also the example
% on the reflexive tactic).

% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Declarations for Coq's API (environment read/write access, etc).
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% tt = Yes, ff = No, unspecified = No (unspecified means "_" or a variable).
typeabbrev opaque?   bool.  macro @opaque! :- tt. macro @transparent! :- ff.

%%%%%%% Attributes to be passed to APIs as in @local! => coq.something %%%%%%%%

macro @global!   :- get-option "coq:locality" "global".
macro @local!    :- get-option "coq:locality" "local".

macro @primitive! :- get-option "coq:primitive" tt. % primitive records

macro @ppwidth! N :- get-option "coq:ppwidth" N. % printing width
macro @ppall! :- get-option "coq:pp" "all". % printing all
macro @ppmost! :- get-option "coq:pp" "most". % printing most of contents

macro @using! S :- get-option "coq:using" S. % like the #[using=S] attribute

% both arguments are strings eg "8.12.0" "use foo instead"
macro @deprecated! Since Msg :-
  get-option "coq:deprecated" (pr Since Msg).

macro @ltacfail! N :- get-option "ltac:fail" N.

% Declaration of inductive types %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

kind indt-decl type.
kind indc-decl type.
kind record-decl type.

% An arity is written, in Coq syntax, as:
%    (x : T1) .. (xn : Tn) : S1 -> ... -> Sn -> U
% This syntax is used, for example, in the type of an inductive type or
% in the type of constructors. We call the abstractions on the left of ":"
% "parameters" while we call the type following the ":" (proper) arity.

% Note: in some contexts, like the type of an inductive type constructor,
% Coq makes no distinction between these two writings
%    (xn : Tn) : forall y1 : S1, ...    and      (xn : Tn) (y1 : S1) : ...
% while Elpi is a bit more restrictive, since it understands user directives
% such as the implicit status of an arguments (eg, using {} instead of () around
% the binder), only on parameters.
% Moreover parameters carry the name given by the user as an "id", while binders
% in terms only carry it as a "name", an irrelevant pretty pringintg hint (see
% also the HOAS of terms). A user command can hence only use the names of
% parameters, and not the names of "forall" quantified variables in the arity.
%
% See also the arity->term predicate in coq-lib.elpi

type parameter id -> implicit_kind -> term -> (term -> arity) -> arity.
type arity term -> arity.

type parameter   id -> implicit_kind -> term -> (term -> indt-decl) -> indt-decl.
type inductive   id -> bool -> arity -> (term -> list indc-decl) -> indt-decl. % tt means inductive, ff coinductive
type record      id -> term -> id -> record-decl -> indt-decl.

type constructor id -> arity -> indc-decl.

type field       field-attributes -> id -> term -> (term -> record-decl) -> record-decl.
type end-record  record-decl.

% Example.
% Remark that A is a regular parameter; y is a non-uniform parameter and t
% also features an index of type bool.
%
%  Inductive t (A : Type) | (y : nat) : bool -> Type :=
%  | K1 (x : A) {n : nat} : S n = y -> t A n true -> t A y true
%  | K2 : t A y false
%
% is written
%
%  (parameter "A" explicit {{ Type }} a\
%     inductive "t" tt (parameter "y" explicit {{ nat }} _\
%                     arity {{ bool -> Type }})
%      t\
%       [ constructor "K1"
%          (parameter "y" explicit {{ nat }} y\
%           (parameter "x" explicit a x\
%            (parameter "n" maximal {{ nat }} n\
%              arity {{ S lp:n = lp:y -> lp:t lp:n true -> lp:t lp:y true }})))
%       , constructor "K2"
%          (parameter "y" explicit {{ nat }} y\
%            arity {{ lp:t lp:y false }}) ])
%
% Remark that the uniform parameters are not passed to occurrences of t, since
% they never change, while non-uniform parameters are both abstracted
% in each constructor type and passed as arguments to t.
%
% The coq.typecheck-indt-decl API can be used to fill in implicit arguments
% an infer universe constraints in the declaration above (e.g. the hidden
% argument of "=" in the arity of K1).
%
% Note: when and inductive type declaration is passed as an argument to an
% Elpi command non uniform parameters must be separated from the uniform ones
% with a | (a syntax introduced in Coq 8.12 and accepted by coq-elpi since
% version 1.4, in Coq this separator is optional, but not in Elpi).

% Context declaration (used as an argument to Elpi commands)
kind context-decl type.
% Eg. (x : T) or (x := B), body is optional, type may be a variable
type context-item  id -> implicit_kind -> term -> option term -> (term -> context-decl) -> context-decl.
type context-end   context-decl.

typeabbrev field-attributes (list field-attribute).

% retrocompatibility macro for Coq v8.10
macro @coercion! :- [coercion tt].
|}
