From elpi Require Import elpi.
From elpi.apps Require Import tc.

#[arguments(raw)] Elpi Tactic TC.TabledSolver.
Elpi TC Solver Register TC.TabledSolver.

(* Tabled type class : https://github.com/purefunctor/tabled-typeclass-resolution?tab=readme-ov-file *)
(* https://github.com/purefunctor/tabled-typeclass-resolution/blob/main/src/lib.rs *)
(* ty = https://github.com/leanprover/lean4/blob/cade21/src/Lean/Expr.lean#L152-L165 *)
(* Coq-Stlc: https://lpcic.github.io/coq-elpi/stlc.txt *) 
Elpi Accumulate lp:{{
  typeabbrev ty term.

  kind data type.
  type data ty -> list data -> data.

  kind assertion type.
  type assertion term -> term -> assertion.

  kind consumer_node type.
  type consumer_node assertion -> list assertion -> consumer_node.

  kind waiter type.
  type root waiter.
  type callback consumer_node -> waiter.

  kind entry type.
  type entry list waiter -> list assertion -> entry.

  typeabbrev resume_stack (list (pair consumer_node assertion)).

  typeabbrev instance tc-instance.

  kind class_instances type.
  type class_instances std.map assertion (list instance) -> class_instances.

  kind generator_node type.
  type generator_node assertion -> list instance -> generator_node.

  kind synth type.
  type synth list generator_node ->
    resume_stack ->
    std.map assertion entry ->
    option assertion ->
    synth.
}}.

Elpi Accumulate lp:{{
  pred type_equal i:ty i:ty o:cmp.
  type_equal X Y eq :- 
    coq.unify-eq X Y ok, !.
  type_equal X Y lt :-
    coq.unify-leq X Y ok, !.
  type_equal _ _ gt.

  pred assertion_equal i:assertion i:assertion o:cmp.
  assertion_equal (assertion A _) (assertion B _) Cmp :-
    coq.say "Assertions equal?" A B,
    type_equal A B Cmp.

  pred term_typeclass i:term o:gref.
  term_typeclass (global Name) Name.
  term_typeclass (app [X | _]) N :- term_typeclass X N.

  pred assertion_typeclass i:assertion o:gref.
  assertion_typeclass (assertion G _) Name :- term_typeclass G Name.
}}.

Elpi Accumulate lp:{{
  pred new_subgoal i:synth i:assertion i:waiter o:synth.
  new_subgoal
    (synth GeneratorStack ResumeStack AssertionTable RootAnswer)
    Subgoal Waiter
    (synth NewGeneratorStack ResumeStack NewAssertionTable RootAnswer) :-
    coq.say "Enter" Subgoal Waiter,
    std.map.add Subgoal (entry [Waiter] []) AssertionTable NewAssertionTable,
    coq.say "AssertionTable" NewAssertionTable,
    assertion_typeclass Subgoal Name,
    coq.TC.db-for Name Instances,
    coq.say "New Subgoal" Name Instances,
    NewGeneratorStack = [(generator_node Subgoal Instances) | GeneratorStack]
    .
}}.

Elpi Accumulate lp:{{
  pred temp_fun i:consumer_node i:assertion o:(pair consumer_node assertion).
  temp_fun A B (pr A B).

  pred waiter_fun i:assertion i:assertion i:waiter i:(pair (resume_stack) (option assertion)) o:(pair (resume_stack) (option assertion)).
  waiter_fun Answer _ root (pr A _) (pr A (some Answer)) :- coq.say "Found answer" Answer.
  waiter_fun _ Goal (callback C) (pr A R) (pr [pr C Goal | A] R) :- coq.say "Run Waiter".

  pred new_consumer_node i:synth i:assertion i:consumer_node o:synth.
  new_consumer_node
      (synth GeneratorStack ResumeStack AssertionTable RootAnswer)
      Answer
      (consumer_node Goal [])
      (synth GeneratorStack NewResumeStack NewAssertionTable NewRootAnswer) :-
    coq.say "Empty node, keep waiters?" Goal "Table" AssertionTable,
    /* for each solution to g, push new cnode onto resume stack with it */
    std.map.find Goal AssertionTable (entry Waiters Answers),
    coq.say "Found Goal",
    /* add new cnode to g's dependents */
    /* TODO: Add answer here! */
    NewAnswers = [ Answer | Answers ],
    coq.say "Fold and readd?",
    /* for each solution to g, push new cnode onto resume stack with it */
    std.fold Waiters (pr ResumeStack RootAnswer) (waiter_fun Answer Goal) (pr NewResumeStack NewRootAnswer),
    /* add new cnode to g's dependents */
    std.map.add Goal (entry Waiters NewAnswers) AssertionTable NewAssertionTable, /* TODO: [] or Waiters? */
    coq.say "Success" NewAssertionTable.

  new_consumer_node
      (synth GeneratorStack ResumeStack AssertionTable RootAnswer)
      _
      CN
      (synth NewGeneratorStack NewResumeStack NewAssertionTable RootAnswer) :-
      CN = consumer_node _ [Subgoal | _ ],
      coq.say "Consumer node" CN, /* TODO: Consumer node is general instead of variable or hole */
      (((std.map.find Subgoal AssertionTable (entry Waiters Answers)),!,
        (
        coq.say "In map" Subgoal AssertionTable (entry Waiters Answers),
        std.map Answers (temp_fun CN) TempResumeStack,
        std.append TempResumeStack ResumeStack NewResumeStack,

        NewWaiters = [ callback CN | Waiters ],
        std.map.add Subgoal (entry NewWaiters Answers) AssertionTable NewAssertionTable,
        NewGeneratorStack = GeneratorStack
        ));
       (
        coq.say "Not in map" Subgoal AssertionTable,
        new_subgoal
           (synth GeneratorStack ResumeStack AssertionTable RootAnswer)
           Subgoal
           (callback CN)
           (synth NewGeneratorStack NewResumeStack NewAssertionTable RootAnswer)
        )
      ),
      coq.say "<- Success".

    new_consumer_node _ _ _ _ :- coq.error "Failed new consumer node!" , fail.
}}.

Elpi Accumulate lp:{{
  pred try_answer_type i:ty o:ty.
  try_answer_type X Y :- coq.unify-eq X Y ok.

  pred try_answer i:assertion o:assertion.
  try_answer (assertion A _) (assertion B _) :-
    coq.say "Try answer A" A "and B" B,
    coq.unify-eq X Y ok.
}}.

Elpi Accumulate lp:{{
  pred tc_instance_to_term i:tc-instance o:term.
  tc_instance_to_term (tc-instance (const C) _) T :-
    coq.env.const C Body Type,
    coq.gref->string (const C) Name,
    T = Type.

  pred try_resolve_types i:term i:term i:term o:list assertion.
  try_resolve_types A ATm (prod X T F) L :-
    !,
    ((T = app [ _ | _ ], !, L = [ assertion T NewV | LS ]) ; (L = LS)),
    try_resolve_types A ATm (F V) LS,
    coq.say "V" V,
    coq.elaborate-skeleton V T NewV ok,
    coq.say "NewV" NewV,
    (ground_term V; coq.say "NOT GROUNHD" V)
    .
  try_resolve_types A ATm B [] :-
    !,
    @holes! ==> coq.unify-leq A B ok
    .

  pred try_resolve i:assertion i:instance o:list assertion.
  try_resolve (assertion A ATm) (tc-instance BI _) RL :-
    tc_instance_to_term (tc-instance BI _) B,
    coq.env.global BI ATm,
    coq.say "ATm" ATm,
    try_resolve_types A ATm B RL
    .
}}.

Elpi Query lp:{{
  coq.unify-leq V {{ nat }} ok. 
}}.

Class R1 (X : Type) (Y : Type).
Axiom A1 B1 C1 D1 : Type.
Instance I1 : R1 A1 B1 := {}. 
Instance I2 : R1 A1 C1 := {}. 
Instance I3 : R1 C1 D1 := {}. 
Instance I4 {X Y Z} `{R1 X Y} `{R1 Y Z} : R1 X Z := {}. 

Elpi Query lp:{{
  coq.TC.db-tc [ R | _ ],
  coq.TC.db-for R [ _ , _ , _ , I4 ],
  try_resolve (assertion {{ R1 A1 D1 }} {{ _ }}) I4 L,
  coq.say {{ I4 }}, 
  coq.say "L" L "vs" [ assertion {{ R1 A1 lp:{{X}} }} _ , assertion {{ R1 lp:{{X}} D1 }} {{ _ }} ],
  L = [ assertion {{ R1 A1 _ }} _ , assertion {{ R1 _ D1 }} _ ],
  coq.say "Subgoals" L.
}}.

Elpi Query lp:{{
  coq.TC.db-tc [ R | _ ],
  coq.TC.db-for R [ _ , _ , I1 , _ ],
  try_resolve (assertion {{ R1 A1 B1 }} {{ _ }}) I1 L,
  coq.say "Subgoals" L.
}}.

Elpi Accumulate lp:{{
  pred tabled_typeclass_resolution_body i:synth i:assertion o:synth o:assertion.
  tabled_typeclass_resolution_body (synth _ _ _ (some Answer)) _ _ Answer.

  tabled_typeclass_resolution_body
    (synth GeneratorStack [ (pr (consumer_node Goal [ Subgoal | Remaining ]) Answer) | ResumeStack ]
       AssertionTable RootAnswer) Query MySynth FinalAnswer :-
    coq.say "ResumeStack" Subgoal Answer,
    (
      (try_answer Subgoal Answer, !,
       coq.say "Suceed try",
       new_consumer_node
         (synth GeneratorStack ResumeStack AssertionTable RootAnswer)
         Answer
         (consumer_node Goal Remaining) /* TODO: Was Goal in code, but should add new solution? */
         MySynth
      );
      (
        coq.say "Continues",
        MySynth = (synth GeneratorStack ResumeStack AssertionTable RootAnswer)
      )
    ).

  tabled_typeclass_resolution_body
    (synth GeneratorStack [ (pr (consumer_node Goal []) Answer) | ResumeStack ]
       AssertionTable RootAnswer) Query MySynth FinalAnswer :-
   coq.say "Cannot resume with empty subgoals!",
   fail.

  tabled_typeclass_resolution_body
    (synth [ generator_node Goal [Instance | Instances ] | GeneratorStack ]
      ResumeStack AssertionTable RootAnswer) Query NewSynth FinalAnswer :-
    (
      (
        /* else (l. 14) */
        coq.say "Try to resolve" Goal Instance,
        try_resolve Goal Instance Subgoals, !,
        coq.say "Resolved" Subgoals,
        /* Instance = instance Answer, */
        (new_consumer_node
          (synth [ generator_node Goal Instances | GeneratorStack ] ResumeStack AssertionTable RootAnswer)
          Goal /* TODO: does not follow protocol! dummy value? */
          (consumer_node Goal Subgoals) NewSynth), /* TODO: Should not be goal but answer? */
        coq.say "No fall trhough"
      );
      (
        /* If first subgoal of cnode does not resolve with solution then Continue */
        coq.say "Fall through",
        NewSynth = (synth [ generator_node Goal Instances | GeneratorStack ] ResumeStack AssertionTable RootAnswer)
      )
    ).

  tabled_typeclass_resolution_body
    (synth [ generator_node _ [] | GeneratorStack ] ResumeStack AssertionTable RootAnswer)
      Query
      (synth GeneratorStack ResumeStack AssertionTable RootAnswer)
      FinalAnswer.
  /* If cnode has no remaining subgoals then (ll.7-13) .. */

  tabled_typeclass_resolution_body (synth [] [] _ _) _ _ _ :- fail.
}}.

Elpi Accumulate lp:{{
  pred synth_loop i:synth i:assertion i:int o:assertion.
  synth_loop (synth _ _ _ (some Answer)) _ Fuel Answer.
  synth_loop MySynth Query Fuel FinalAnswer :-
    coq.say Fuel MySynth,
    Fuel > 0,
    tabled_typeclass_resolution_body MySynth Query NextSynth FinalAnswer,
    !,
    NextFuel is Fuel - 1,
    synth_loop NextSynth Query NextFuel FinalAnswer.

  pred tabled_typeclass_resolution i:assertion o:assertion.
  tabled_typeclass_resolution Query FinalAnswer :-
    coq.say "Query?" Query,
    std.map.make assertion_equal AssertionTableEmpty,
    new_subgoal (synth [] [] AssertionTableEmpty none) Query root MySynth,
    /* while true do */
    synth_loop MySynth Query 2000 FinalAnswer.
}}.

(*
Class R (X : Type) (Y : Type).
Axiom A B C D : Type.
Instance I1 : R A B := {}. 
Instance I2 : R A C := {}. 
Instance I3 : R C D := {}. 
Instance I4 {X Y Z} `{R X Y} `{R Y Z} : R X Z := {}. 
 *)

(* Trivial Example *)
Elpi Query lp:{{ 
  MyGoal = {{ R1 A1 B1 }},
  tabled_typeclass_resolution (assertion MyGoal {{ _ }}) FinalAnswer,
  coq.say "FinalAnswer" FinalAnswer.
}}.

(* Example from Paper *)
Elpi Query lp:{{ 
  MyGoal = {{ R1 A1 D1 }},
  tabled_typeclass_resolution (assertion MyGoal {{ _ }}) FinalAnswer,
  coq.say "FinalAnswer" FinalAnswer.
}}.

(* Example that should fail *)
Axiom E : Type.
(*,
Elpi Query lp:{{
  MyGoal = assertion {{ R A E }},
  (tabled_typeclass_resolution MyGoal FinalAnswer),
  coq.say "Finished" FinalAnswer.
  not (tabled_typeclass_resolution MyGoal FinalAnswer),
  coq.say "Finished" FinalAnswer.
}}.
 *)

(* https://github.com/leanprover/lean4/blob/cade21/src/Lean/Meta/SynthInstance.lean *)
(* https://github.com/leanprover/lean4/blob/master/tests/lean/run/typeclass_diamond.lean *)
(* Diamond *)

(*
Elpi Query lp:{{
  MyLInstances = [
    instance (assertion "L" [ty_variable "alpha", ty_variable "n"] none) [assertion "B" [ty_variable "alpha", ty_variable "n"] none] ],

  MyRInstances = [
    instance (assertion "R" [ty_variable "alpha", ty_variable "n"] none) [assertion "B" [ty_variable "alpha", ty_variable "n"] none] ],

  MyTInstances = [
    instance (assertion "T" [ty_variable "alpha", ty_variable "n"] none) [assertion "L" [ty_variable "alpha", ty_variable "n"] none],
    instance (assertion "T" [ty_variable "alpha", ty_variable "n"] none) [assertion "R" [ty_variable "alpha", ty_variable "n"] none] ],

  MyBInstances = [
    instance (assertion "B" [ty_variable "alpha", ty_constructor "0"] none) [],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "1"] none) [assertion "T" [ty_variable "alpha", ty_constructor "0"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "2"] none) [assertion "T" [ty_variable "alpha", ty_constructor "1"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "3"] none) [assertion "T" [ty_variable "alpha", ty_constructor "2"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "4"] none) [assertion "T" [ty_variable "alpha", ty_constructor "3"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "5"] none) [assertion "T" [ty_variable "alpha", ty_constructor "4"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "6"] none) [assertion "T" [ty_variable "alpha", ty_constructor "5"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "7"] none) [assertion "T" [ty_variable "alpha", ty_constructor "6"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "8"] none) [assertion "T" [ty_variable "alpha", ty_constructor "7"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "9"] none) [assertion "T" [ty_variable "alpha", ty_constructor "8"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "10"] none) [assertion "T" [ty_variable "alpha", ty_constructor "9"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "11"] none) [assertion "T" [ty_variable "alpha", ty_constructor "10"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "12"] none) [assertion "T" [ty_variable "alpha", ty_constructor "11"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "13"] none) [assertion "T" [ty_variable "alpha", ty_constructor "12"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "14"] none) [assertion "T" [ty_variable "alpha", ty_constructor "13"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "15"] none) [assertion "T" [ty_variable "alpha", ty_constructor "14"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "16"] none) [assertion "T" [ty_variable "alpha", ty_constructor "15"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "17"] none) [assertion "T" [ty_variable "alpha", ty_constructor "16"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "18"] none) [assertion "T" [ty_variable "alpha", ty_constructor "17"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "19"] none) [assertion "T" [ty_variable "alpha", ty_constructor "18"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "20"] none) [assertion "T" [ty_variable "alpha", ty_constructor "19"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "21"] none) [assertion "T" [ty_variable "alpha", ty_constructor "20"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "22"] none) [assertion "T" [ty_variable "alpha", ty_constructor "21"] none],
    instance (assertion "B" [ty_variable "alpha", ty_constructor "23"] none) [assertion "T" [ty_variable "alpha", ty_constructor "22"] none],
  ],

  std.map.make cmp_term ClassInstancesTemp1,
  std.map.add "L" MyLInstances ClassInstancesTemp1 ClassInstancesTemp2,
  std.map.add "R" MyRInstances ClassInstancesTemp2 ClassInstancesTemp3,
  std.map.add "T" MyTInstances ClassInstancesTemp3 ClassInstancesTemp4,
  std.map.add "B" MyBInstances ClassInstancesTemp4 ClassInstancesTemp5,
  ClassInstances = ClassInstancesTemp5,

  MyGoal = (assertion "T" [ty_constructor "Unit", ty_constructor "23"] none),

  coq.say "Almost" MyGoal ClassInstances,
  tabled_typeclass_resolution MyGoal ClassInstances FinalAnswer,
  coq.say "Finished" FinalAnswer.
}}.
*)

(* https://github.com/LPCIC/coq-elpi/blob/master/builtin-doc/coq-builtin.elpi *)
Elpi Accumulate lp:{{
  pred proof_search i:list gref i:list tc-instance i:term o:term.
  proof_search Typeclasses [tc-instance Hd _ | _ ] Type PRoof :-
    coq.env.typeof Hd TypeRes,
    coq.env.global Hd ProofRes,
    coq.say "CHECKING" TypeRes,
    coq.unify-eq TypeRes Type D,
    coq.say D,
    D = ok,
    % TypeRes = Type,
    coq.say "SUCCESS",
    PRoof = ProofRes.
  proof_search Typeclasses [_|Tl] Type PRoof :-
    proof_search Typeclasses Tl Type PRoof.
}}.

Elpi Accumulate lp:{{
  pred tabled_proof_search i:list gref i:term o:term.
  tabled_proof_search Typeclasses Type PRoof :-
    coq.say "TYPECLASSES" Typeclasses,
    coq.say "TYPE" Type,
    /*
    std.map.make cmp_term ClassInstancesTemp,
    std.fold Typeclasses ClassInstancesTemp fold_class_instances ClassInstances, 
    */
    MyGoal = assertion Type {{ _ }},
    /* term_to_assertion Type none MyGoal, /* MyGoal is Assertion */ */
    coq.say "Goal" MyGoal,
    coq.say "Attemp" MyGoal ClassInstances,
    tabled_typeclass_resolution MyGoal FinalAnswer,
    !,
    coq.say "Final Answer" FinalAnswer,

    /* TODO: Convert from result to proof term! */

    FinalAnswer = assertion FinalType FinalTerm,
    FinalProof = FinalTerm,
    coq.say "FinalProof" FinalProof,
    PRoof = FinalProof,
    coq.say "Proof" PRoof,

    coq.say "Done".


  pred search_context i:list prop i:term o:term.
  search_context [decl Te N Ty | _] Type PRoof :-
    Ty = Type,
    Te = PRoof,
    coq.say "CHECK SUCC" N PRoof.
  search_context [_|Tl] Type PRoof :- search_context Tl Type PRoof.

  solve (goal Ctx Trigger Type PRoof Args as G) V :-
    coq.TC.db-tc Typeclasses,
    coq.say "AGRS" Args Ctx,
    coq.say "SEARCHING ..." Type, !,
    coq.say "V" V,
    (search_context Ctx Type PRoof ; tabled_proof_search Typeclasses Type PRoof),
    coq.say "SUCCESS FINDING INSTANCE".
    

  solve _ _ :- coq.ltac.fail _ "No auto".
}}.

Elpi TC Solver Activate TC.TabledSolver.
Elpi TC Solver Override TC.TabledSolver All.

Elpi Export TC.TabledSolver.

(* Trivial test *)
Class Constant := {}.
Instance Con : Constant := {}.
(* Instance TestConstant : Constant := _. *)

(* Check holes *)
Elpi Query lp:{{
  /* {{ Instance TestConstant : Constant := _ }} */
  coq.elaborate-skeleton {{ lib:elpi.hole }} {{ Constant }} V ok,
  coq.say "Elaborates to" V.
}}.

(* Test instance dependency *)
Class Dependency := {}.

Instance Dep `{Constant} : Dependency := {}.

Elpi Query lp:{{
  /* {{ Instance TestConstant : Constant := _ }} */
  coq.elaborate-skeleton {{ lib:elpi.hole }} {{ Constant }} V ok,
  coq.say "Elaborates to" V.
}}.

(*
Elpi Query lp:{{ 
  coq.say "Dep" {{ Constant }},
  coq.elaborate-skeleton {{ lib:elpi.hole }} {{ Constant }} _ ok, !,
  coq.elaborate-skeleton {{ lib:elpi.hole }} {{ Dependency }} _ ok. 
}}.
*)

(* Instance TestDependency : Dependency := _. *)

(* Trivial test *)
Class Argument (alpha : Type) := {}.
Instance Arg : Argument unit := {}.
Instance TestArgument : Argument unit := _.

Instance AArg (alpha : Type) : Argument alpha := {}.
(* Instance TestArgumentArg : Argument nat := _. *)

(* Partial Simple Diamond example *)
Class T (n : nat).
Class R (n : nat).
Class L (n : nat).
Class B (n : nat).
Instance BtL n `{B n} : L n := {}.
Instance BtR n `{B n} : R n := {}.
Instance LtR n `{L n} : T n := {}.
Instance RtR n `{R n} : T n := {}.

Instance B0 : B 0 := {}.

Instance Test0 : B 0 := _.
Instance Test100 : B 10 := _.

(* Partial Diamond example *)
Class T (alpha : Type) (n : nat).
Class R (alpha : Type) (n : nat).
Class L (alpha : Type) (n : nat).
Class B (alpha : Type) (n : nat).
Instance BtL alpha n `{B alpha n} : L alpha n := {}.
Instance BtR alpha n `{B alpha n} : R alpha n := {}.
Instance LtR alpha n `{L alpha n} : T alpha n := {}.
Instance RtR alpha n `{R alpha n} : T alpha n := {}.

Instance B0 alpha : B alpha 0 := {}.

Instance Test0 : B unit 0 := _.

(* Diamond example in Rocq *)
Class T (alpha : Type) (n : nat).
Class R (alpha : Type) (n : nat).
Class L (alpha : Type) (n : nat).
Class B (alpha : Type) (n : nat).
Instance BtL alpha n `{B alpha n} : L alpha n := {}.
Instance BtR alpha n `{B alpha n} : R alpha n := {}.
Instance LtR alpha n `{L alpha n} : T alpha n := {}.
Instance RtR alpha n `{R alpha n} : T alpha n := {}.
Instance TtR alpha n `{T alpha n} : B alpha (S n) := {}.

Instance B0 alpha : B alpha 0 := {}.

Fail Instance TtR20 : B unit 20 := _.
