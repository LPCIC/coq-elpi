From elpi Require Import elpi.
From elpi.apps Require Import tc.

#[arguments(raw)] Elpi Tactic TC.TabledSolver.
Elpi TC Solver Register TC.TabledSolver.

(* Tabled type class : https://github.com/purefunctor/tabled-typeclass-resolution?tab=readme-ov-file *)
(* https://github.com/purefunctor/tabled-typeclass-resolution/blob/main/src/lib.rs *)
(* ty = https://github.com/leanprover/lean4/blob/cade21/src/Lean/Expr.lean#L152-L165 *)
(* Coq-Stlc: https://lpcic.github.io/coq-elpi/stlc.txt *)
(* https://github.com/leanprover/lean4/blob/master/src/Lean/Expr.lean#L302-L512 *)
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
  type_equal X Y eq :- var X, var Y.
  type_equal (app L) (app G) Cmp :- type_equal_list L G Cmp.
  type_equal X Y lt :- var X, ground_term Y.
  type_equal X Y gt :- ground_term X, var Y.
  type_equal X Y Cmp :-
    ground_term X,
    ground_term Y,
    cmp_term X Y Cmp.

  pred type_equal_list i:list ty i:list ty o:cmp.
/* std.map L (x\ y\ type_equal x y eq) G. */
  type_equal_list [ X | XS ] [ Y | YS ] Cmp :-
      type_equal X Y eq,
      type_equal_list XS YS Cmp.
  type_equal_list [ X | _ ] [ Y | _ ] Cmp :-
      type_equal X Y Cmp,
      not (Cmp = eq).
  type_equal_list [] [] eq.


  pred assertion_equal i:assertion i:assertion o:cmp.
  assertion_equal (assertion A _) (assertion B _) Cmp :-
  /* coq.say "Assertions equal?" A B, */
    type_equal A B Cmp.

  pred term_typeclass i:term o:gref.
  term_typeclass (global Name) Name.
  term_typeclass (app [X | _]) N :- term_typeclass X N.
  term_typeclass (prod X T F) N :-
    pi x\ term_typeclass (F x) N.

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
    /* coq.say "New Subgoal" Name Instances, */
    NewGeneratorStack = [(generator_node Subgoal Instances) | GeneratorStack]
    .
}}.

(* Apply answer to goal and update meta variable context if it succeeds *)
Elpi Accumulate lp:{{
  pred replace_var_term i:ty o:ty i:ty o:ty.
  replace_var_term X Y (app L) (app G) :-
    std.map L (replace_var_term X Y) G.
  replace_var_term X Y Z W :-
    var Z,
    X == Z,
    W = Y
    .
  replace_var_term X Y Z Z.

  pred replace_var_in_list i:ty o:ty i:list assertion o:list assertion.
  replace_var_in_list X Y [ assertion TA VA | AS ] [ assertion TB VB | BS ] :-
      replace_var_term X Y TA TB,
      replace_var_term X Y VA VB,
      replace_var_in_list X Y AS BS.
  replace_var_in_list _ _ [] [].

  pred try_answer_type i:ty o:ty i:ty o:ty i:list assertion o:list assertion.
  try_answer_type X Y IX IY Lin Lout :-
    var X, var Y,
    replace_var_term X Y IX IY,
    replace_var_in_list X Y Lin Lout.
  try_answer_type (app L) (app G) IX IY Lin Lout :-
    try_answer_type_list L G IX IY Lin Lout.
  try_answer_type X Y IX IY Lin Lout :-
    var X, ground_term Y, replace_var_term X Y IX IY, replace_var_in_list X Y Lin Lout.
  try_answer_type X Y I I L L :-
    ground_term X,
    ground_term Y,
    cmp_term X Y eq.

  pred try_answer_type_list i:list ty o:list ty i:ty o:ty i:list assertion o:list assertion.
  try_answer_type_list [ X | XS ] [ Y | YS ] IX IY Lin Lout :-
      try_answer_type X Y IX Itemp Lin Ltemp,
      try_answer_type_list XS YS Itemp IY Ltemp Lout.
  try_answer_type_list [] [] I I L L.

  pred try_answer i:assertion o:assertion i:assertion o:assertion i:list assertion o:list assertion.
  try_answer (assertion A VA) (assertion B VB) (assertion G IA) (assertion G IB) Lin Lout :-
    coq.say "Try answer",
    coq.say "A" A VA,
    coq.say "B" B VB,
    try_answer_type A B IA ITemp Lin Lout,
    replace_var_term VA VB ITemp IB,
    coq.say "IAB" IA IB,
    coq.sigma.print.
}}.

Elpi Accumulate lp:{{
  pred replace_list i:list term i:term i:term o:list term.
  replace_list [ A | XS ] A B [ B | YS ] :-
      !,
      replace_list XS A B YS.
  replace_list [ C | XS ] A B [ C | YS ] :-
      replace_list XS A B YS.
  replace_list [] _ _ [].

  pred extract_helper i:term i:int i:term o:term.
  extract_helper X Index (prod N T F) (prod N T G) :-
    !,
    pi x\
      extract_helper X Index (F x) (G x).
  extract_helper X Index (app L) (app NewL) :-
    !,
    std.split-at Index L Lfront [ V | Ltail ],
    replace_list L V X NewL.

  pred is_var_at_index i:term i:int.
  is_var_at_index (prod N T F) I :-
    pi x\
      is_var_at_index (F x) I.
  is_var_at_index (app L) I :-
    std.split-at I L Lfront [ T | Ltail],
    var T.

  pred extract_variables i:list term i:int o:term.
    extract_variables L -1 (app L).
  extract_variables L Index Tm :-
    PrevIndex is Index - 1,
    extract_variables L PrevIndex PrevTm,
    !,
    ((is_var_at_index PrevTm Index,
     Tm = prod TmX TmT TmF,
     pi x\
       extract_helper x Index PrevTm (TmF x)
    );
    (Tm = PrevTm))
    .

  pred re_generalize i:list term o:list term.
  re_generalize [ X | Tl ] R :-
    coq.typecheck X T ok,
    (
      (T = (app Tlist),
       std.length Tlist Len,
       Index is Len - 1,
       extract_variables Tlist Index NewR,
       R = [ NewR | RTl ],
       coq.say "NewR" NewR
       );
      (R = RTl)
    ),
    re_generalize Tl RTl
    .
  re_generalize [ X | Tl ] [] :-
    re_generalize Tl R.
  re_generalize [ ] [].
}}.


Elpi Accumulate lp:{{
  pred tc_instance_to_term i:tc-instance o:term.
  tc_instance_to_term (tc-instance (const C) _) T :-
    coq.env.const C _ /* Body */ Type,
    coq.gref->string (const C) _ /* Name */,
    T = Type.

  pred does_type_resolve i:term o:term.
  does_type_resolve X Y :-
    var X.
  does_type_resolve (app L) (app G) :-
    std.map L does_type_resolve G.
  does_type_resolve X Y :-
    ground_term X,
    X = Y.

  pred try_resolve_types i:term i:term o:list term o:list assertion.
  try_resolve_types A (prod X T F) OL L :-
    !,
    coq.typecheck V T ok,
    try_resolve_types A (F V) OLS LS,
    (OL = [ V | OLS]),
    ((ground_term T, L = LS) ; L = [ assertion T V | LS ])
    .
  try_resolve_types A B [] [] :-
    /* @holes! ==> coq.unify-leq B A ok */
    does_type_resolve A B
    /* type_equal A B lt */
    /* cmp_term A B eq */
    /* @holes! ==> pattern_match A B */
    /* @holes! ==> coq.unify-leq B A ok */
    .
}}.

Elpi Accumulate lp:{{
  pred helper_fn i:term o:assertion.
  helper_fn A (assertion A V).

  pred simpl i:term o:term.
  simpl (app [ prod X T F , Arg | Tl ]) R :-
    simpl (app [ (F Arg) | Tl ]) R.
  simpl (app [ A ]) A.
  simpl A A.

  pred filter_metavariables i:list assertion o:list assertion.
  filter_metavariables [ assertion (app L) V | XS ] [ assertion (app L) V | YS ] :-
      !, filter_metavariables XS YS.
  filter_metavariables [ assertion X _ | XS ] YS :-
      filter_metavariables XS YS.
  filter_metavariables [] [].


  pred try_resolve i:assertion i:instance o:assertion o:list assertion.
  try_resolve (assertion A _) (tc-instance BI _) (assertion RT RV) RL :-
    tc_instance_to_term (tc-instance BI _) B,
    coq.env.global BI BITm,
    coq.gref->string BI BIName,
    BI = const (BIConst),
    coq.env.const BIConst (some BIBody) BITy,
    coq.say "Try resolve types" A B,
    try_resolve_types A B OL L,
    /* coq.say "regeneralize" OL L, */
    /* re_generalize L LR, */
    /* coq.say "generalized" LR, */
    filter_metavariables L RL,
    !,
    coq.say "RL" RL,
    RT = A, /* app [ B | OL ], */
    ((OL = [], RV = BITm) ; RV = app [ BITm | OL ]),
    coq.say "Result" RT RV "for" A

    /* ATm = app [ B | OL ],
        simpl ATm ATmRed */
    .
}}.

Elpi Accumulate lp:{{
  pred temp_fun i:consumer_node i:assertion o:(pair consumer_node assertion).
  temp_fun A B (pr A B) :-
    coq.say "Update - Try" A "with answer" B.

  pred waiter_fun i:assertion i:assertion i:waiter i:(pair (resume_stack) (option assertion)) o:(pair (resume_stack) (option assertion)).
  waiter_fun Answer Guess root (pr A _) (pr A (some Answer)) :-
    coq.say "Found root answer" Answer,
    coq.say "Stack" A Guess.
  waiter_fun Answer Goal (callback C) (pr A R) (pr [pr C Answer /* Goal */ | A] R) :-
      coq.say "Found an answer" C Goal Answer,
      coq.say "Run Waiter".

  pred new_consumer_node i:synth i:assertion i:consumer_node o:synth.
  new_consumer_node
      (synth GeneratorStack ResumeStack AssertionTable RootAnswer)
      Answer
      (consumer_node Goal [])
      (synth GeneratorStack NewResumeStack NewAssertionTable NewRootAnswer) :-
    /* for each solution to g, push new cnode onto resume stack with it */
    std.map.find Goal AssertionTable (entry Waiters Answers),
    /* add new cnode to g's dependents */
    /* TODO: Add answer here! */
    NewAnswers = [ Answer | Answers ],
    coq.say "NewAnswers" NewAnswers,
    /* for each solution to g, push new cnode onto resume stack with it */
    std.fold Waiters (pr ResumeStack RootAnswer) (waiter_fun Answer Goal) (pr NewResumeStack NewRootAnswer),
    /* add new cnode to g's dependents */
    std.map.remove Goal AssertionTable TempAssertionTable,
    std.map.add Goal (entry Waiters NewAnswers) TempAssertionTable NewAssertionTable /* TODO: [] or Waiters? */.

  new_consumer_node
      (synth GeneratorStack ResumeStack AssertionTable RootAnswer)
      _
      CN
      (synth NewGeneratorStack NewResumeStack NewAssertionTable RootAnswer) :-
      CN = consumer_node _ [ Subgoal | _ ],
      /* TODO: Consumer node is general instead of variable or hole */
      if (std.map.find Subgoal AssertionTable (entry Waiters Answers))
         (
          /* Map answers with consumer node */
          coq.say "Found subgoal map" Answers,
          /* Add cnode onto G's dependents? */
          std.map Answers (temp_fun CN) TempResumeStack,
          std.append TempResumeStack ResumeStack NewResumeStack,

          NewWaiters = [ callback CN | Waiters ],
          std.map.remove Subgoal AssertionTable TempAssertionTable,
          std.map.add Subgoal (entry NewWaiters Answers) TempAssertionTable NewAssertionTable,
          NewGeneratorStack = GeneratorStack
         )
         (
          new_subgoal
            (synth GeneratorStack ResumeStack AssertionTable RootAnswer)
            Subgoal
            (callback CN)
            (synth NewGeneratorStack NewResumeStack NewAssertionTable RootAnswer)
        ).

    new_consumer_node _ _ _ _ :- coq.error "Failed new consumer node!" , fail.
}}.

Elpi Accumulate lp:{{
  pred tabled_typeclass_resolution_body i:synth i:assertion o:synth o:assertion.
  tabled_typeclass_resolution_body (synth _ _ _ (some Answer)) _ _ Answer.

  tabled_typeclass_resolution_body
    (synth GeneratorStack [ (pr (consumer_node Goal [ Subgoal | Remaining ]) Answer) | ResumeStack ]
       AssertionTable RootAnswer) Query MySynth FinalAnswer :-
    coq.say "ResumeStack" Goal Subgoal Answer,
    Answer = assertion AnswerT AnswerV,
    coq.typecheck AnswerV AnswerNT ok,
    NewAnswer = assertion AnswerNT AnswerV,
    (ground_term Answer; coq.say "Not ground answer"), /* TODO: Should answer be ground? */
    if (try_answer Subgoal NewAnswer Goal UpdatedGoal Remaining UpdatedRemaining)
       (coq.say "Suceed try" Remaining UpdatedRemaining,
       /* TODO: Update Remaining with unification from try_answer ! */
       /* keep goal? clone? */
        coq.say "Actual" Subgoal NewAnswer,
        coq.say "Goal" Goal UpdatedGoal,
        new_consumer_node
         (synth GeneratorStack ResumeStack AssertionTable RootAnswer)
         UpdatedGoal /* TODO: final answer here! */
         (consumer_node UpdatedGoal UpdatedRemaining) /* TODO: Was Goal in code, but should add new solution? */
         MySynth
      )
      (
        coq.say "Continues",
        MySynth = (synth GeneratorStack ResumeStack AssertionTable RootAnswer)
      ).

  tabled_typeclass_resolution_body
    (synth GeneratorStack [ (pr (consumer_node Goal []) Answer) | ResumeStack ]
       AssertionTable RootAnswer) Query MySynth FinalAnswer :-
   coq.say "Cannot resume with empty subgoals!",
   fail.

  tabled_typeclass_resolution_body
    (synth [ generator_node Goal [Instance | Instances ] | GeneratorStack ]
      ResumeStack AssertionTable RootAnswer) Query NewSynth FinalAnswer :-
    if (try_resolve Goal Instance Resolved Subgoals)
        (
        /* else (l. 14) */
        coq.say "Resolved" Goal Resolved "Subgoals" Subgoals,
        (ground_term Resolved ; coq.say "Resolved not ground"),
        (new_consumer_node
          (synth [ generator_node Goal Instances | GeneratorStack ] ResumeStack AssertionTable RootAnswer)
          Resolved /* TODO: does not follow protocol! dummy value? */
          (consumer_node Resolved Subgoals) NewSynth), /* TODO: Should not be goal but answer? */
        coq.say "No fall trhough"
        )
        (
        /* If first subgoal of cnode does not resolve with solution then Continue */
        coq.say "Fall through",
        NewSynth = (synth [ generator_node Goal Instances | GeneratorStack ] ResumeStack AssertionTable RootAnswer)
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
    MySynth = synth Stack1 Stack2 _ _,
    coq.say Fuel Stack2 Stack1,
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
    synth_loop MySynth Query 2000 FinalAnswer,
    !.
}}.

Class R1 (X : Type) (Y : Type).
Axiom A1 B1 C1 D1 : Type.
Instance I3 : R1 C1 D1 := {}.
Instance I2 : R1 A1 C1 := {}.
Instance I1 : R1 A1 B1 := {}.
Instance I4 {X Y Z} `(R1 X Y) `(R1 Y Z) : R1 X Z := { }.

(* Trivial Example *)
Elpi Query lp:{{
  MyGoal = {{ R1 A1 B1 }},
  tabled_typeclass_resolution (assertion MyGoal {{ lib:elpi.hole }}) (assertion FinalType FinalAnswer),
  FinalType = MyGoal,
  coq.say "FinalAnswer" FinalType FinalAnswer,
  coq.typecheck FinalAnswer MyGoal ok.
}}.

(* Instance TestRAB : R1 A1 B1 := _. *)

(* Example from Paper *)
Elpi Query lp:{{
  MyGoal = {{ R1 A1 D1 }},
  coq.say "MyGoal" (assertion MyGoal {{ lib:elpi.hole }}),
  tabled_typeclass_resolution (assertion MyGoal {{ lib:elpi.hole }}) (assertion FinalType FinalAnswer),
  !,
  coq.say "FinalAnswer" FinalType FinalAnswer "vs" {{ @I4 A1 C1 D1 I2 I3 }} {{ I4 I2 I3 }},
  FinalType = MyGoal,
  coq.say "Typechecks?",
  coq.typecheck FinalAnswer MyGoal ok,
  coq.say "Final Ground?",
  ground_term FinalAnswer.
}}.

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

(* Check holes *)
Elpi Query lp:{{
  /* {{ Instance TestConstant : Constant := _ }} */
  coq.elaborate-skeleton {{ lib:elpi.hole }} {{ Constant }} V ok,
  coq.say "Elaborates to" V.
}}.
Instance TestConstant : Constant := _.

(* Test instance dependency *)
Class Dependency := {}.

Instance Dep `{Constant} : Dependency := {}.

Elpi Query lp:{{
  /* {{ Instance TestConstant : Constant := _ }} */
  coq.elaborate-skeleton {{ lib:elpi.hole }} {{ Constant }} V ok,
  coq.say "Elaborates to" V.
}}.

Elpi Query lp:{{
  coq.say "Dep" {{ Constant }},
  coq.elaborate-skeleton {{ lib:elpi.hole }} {{ Constant }} _ ok, !,
  coq.elaborate-skeleton {{ lib:elpi.hole }} {{ Dependency }} V ok,
  coq.say "Elaborates to" V.
}}.

Instance TestDependency : Dependency := _.

(* Trivial test *)
Class Argument (alpha : Type) := {}.
Instance Arg : Argument unit := {}.
Instance TestArgument : Argument unit := _.

Instance AArg (alpha : Type) : Argument alpha := {}.
(* Instance TestArgumentArg : Argument nat := _. *)
