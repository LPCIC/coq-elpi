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
    std.map.add Subgoal (entry [Waiter] []) AssertionTable NewAssertionTable,
    assertion_typeclass Subgoal Name,
    coq.TC.db-for Name Instances,
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
    try_answer_type A B IA ITemp Lin Lout,
    replace_var_term VA VB ITemp IB.
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
       R = [ NewR | RTl ]
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
    coq.say "Test" A X T,
    !,
    coq.typecheck V T ok,
    coq.say "Passed",
    try_resolve_types A (F V) OLS LS,
    (OL = [ V | OLS]),
    ((T = app _ ; L = [ assertion T V | LS ]) ; (L = LS)) /* TODO : better 'contains instance or var test' */
    .
  try_resolve_types A B [] [] :-
    /* @holes! ==> coq.unify-leq B A ok */
    coq.say "Does type resolve" A B,
    does_type_resolve A B,
    coq.say "Yes"
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
    try_resolve_types A B OL L,
    filter_metavariables L RL,
    !,
    RT = A, /* app [ B | OL ], */
    ((OL = [], RV = BITm) ; RV = app [ BITm | OL ])
    .
}}.

Elpi Accumulate lp:{{
  pred temp_fun i:consumer_node i:assertion o:(pair consumer_node assertion).
  temp_fun A B (pr A B).

  pred waiter_fun i:assertion i:assertion i:waiter i:(pair (resume_stack) (option assertion)) o:(pair (resume_stack) (option assertion)).
  waiter_fun Answer Guess root (pr A _) (pr A (some Answer)).
  waiter_fun Answer Goal (callback C) (pr A R) (pr [pr C Answer /* Goal */ | A] R).

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
    Answer = assertion AnswerT AnswerV,
    coq.typecheck AnswerV AnswerNT ok,
    NewAnswer = assertion AnswerNT AnswerV,
    if (try_answer Subgoal NewAnswer Goal UpdatedGoal Remaining UpdatedRemaining)
       (
       /* TODO: Update Remaining with unification from try_answer ! */
       /* keep goal? clone? */
        new_consumer_node
         (synth GeneratorStack ResumeStack AssertionTable RootAnswer)
         UpdatedGoal /* TODO: final answer here! */
         (consumer_node UpdatedGoal UpdatedRemaining) /* TODO: Was Goal in code, but should add new solution? */
         MySynth
      )
      (
        MySynth = (synth GeneratorStack ResumeStack AssertionTable RootAnswer)
      ).

  tabled_typeclass_resolution_body
    (synth GeneratorStack [ (pr (consumer_node Goal []) Answer) | ResumeStack ]
       AssertionTable RootAnswer) Query MySynth FinalAnswer :-
   coq.warn "Cannot resume with empty subgoals!",
   fail.

  tabled_typeclass_resolution_body
    (synth [ generator_node Goal [Instance | Instances ] | GeneratorStack ]
      ResumeStack AssertionTable RootAnswer) Query NewSynth FinalAnswer :-
    if (try_resolve Goal Instance Resolved Subgoals)
        (
        /* else (l. 14) */
        (new_consumer_node
          (synth [ generator_node Goal Instances | GeneratorStack ] ResumeStack AssertionTable RootAnswer)
          Resolved /* TODO: does not follow protocol! dummy value? */
          (consumer_node Resolved Subgoals) NewSynth)
        )
        (
        /* If first subgoal of cnode does not resolve with solution then Continue */
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
    coq.say "synth round" Fuel Stack2 Stack1,
    Fuel > 0,
    tabled_typeclass_resolution_body MySynth Query NextSynth FinalAnswer,
    !,
    NextFuel is Fuel - 1,
    synth_loop NextSynth Query NextFuel FinalAnswer.

  pred tabled_typeclass_resolution i:assertion o:assertion.
  tabled_typeclass_resolution Query FinalAnswer :-
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
    MyGoal = assertion Type {{ _ }},
    /* term_to_assertion Type none MyGoal, /* MyGoal is Assertion */ */
    tabled_typeclass_resolution MyGoal FinalAnswer,
    !,
    coq.say "Final Answer" FinalAnswer,
    FinalAnswer = assertion FinalType FinalTerm,
    FinalProof = FinalTerm,
    coq.say "FinalProof" FinalProof,
    PRoof = FinalProof,
    coq.say "Proof" PRoof "Done".


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

(* Instance TestDependency : Dependency := _. *)

(* Trivial test *)
Class Argument (alpha : Type) := {}.
Instance Arg : Argument unit := {}.
Instance TestArgument : Argument unit := _.

Instance AArg (alpha : Type) : Argument alpha := {}.
Instance TestArgumentArg : Argument nat := _.

(* Direct Simple Diamond example *)
Class TD (n : nat).
Class RD (n : nat).
Class LD (n : nat).
Class BD (n : nat).

Instance BD0 : BD 0 := {}.

Instance BtL0 `{BD 0} : LD 0 := {}.
Instance BtR0 `{BD 0} : RD 0 := {}.
Instance LtR0 `{LD 0} : TD 0 := {}.
Instance RtR0 `{RD 0} : TD 0 := {}.
Instance Ttb0 `{TD 0} : BD (S 0) := {}.

Instance BtL1 `{BD 1} : LD 1 := {}.
Instance BtR1 `{BD 1} : RD 1 := {}.
Instance LtR1 `{LD 1} : TD 1 := {}.
Instance RtR1 `{RD 1} : TD 1 := {}.
Instance Ttb1 `{TD 1} : BD (S 1) := {}.

Instance BtL2 `{BD 2} : LD 2 := {}.
Instance BtR2 `{BD 2} : RD 2 := {}.
Instance LtR2 `{LD 2} : TD 2 := {}.
Instance RtR2 `{RD 2} : TD 2 := {}.
Instance Ttb2 `{TD 2} : BD (S 2) := {}.

Instance BtL3 `{BD 3} : LD 3 := {}.
Instance BtR3 `{BD 3} : RD 3 := {}.
Instance LtR3 `{LD 3} : TD 3 := {}.
Instance RtR3 `{RD 3} : TD 3 := {}.
Instance Ttb3 `{TD 3} : BD (S 3) := {}.

Instance BtL4 `{BD 4} : LD 4 := {}.
Instance BtR4 `{BD 4} : RD 4 := {}.
Instance LtR4 `{LD 4} : TD 4 := {}.
Instance RtR4 `{RD 4} : TD 4 := {}.
Instance Ttb4 `{TD 4} : BD (S 4) := {}.

Instance BtL5 `{BD 5} : LD 5 := {}.
Instance BtR5 `{BD 5} : RD 5 := {}.
Instance LtR5 `{LD 5} : TD 5 := {}.
Instance RtR5 `{RD 5} : TD 5 := {}.
Instance Ttb5 `{TD 5} : BD (S 5) := {}.

Instance BtL6 `{BD 6} : LD 6 := {}.
Instance BtR6 `{BD 6} : RD 6 := {}.
Instance LtR6 `{LD 6} : TD 6 := {}.
Instance RtR6 `{RD 6} : TD 6 := {}.
Instance Ttb6 `{TD 6} : BD (S 6) := {}.

Instance BtL7 `{BD 7} : LD 7 := {}.
Instance BtR7 `{BD 7} : RD 7 := {}.
Instance LtR7 `{LD 7} : TD 7 := {}.
Instance RtR7 `{RD 7} : TD 7 := {}.
Instance Ttb7 `{TD 7} : BD (S 7) := {}.

Instance BtL8 `{BD 8} : LD 8 := {}.
Instance BtR8 `{BD 8} : RD 8 := {}.
Instance LtR8 `{LD 8} : TD 8 := {}.
Instance RtR8 `{RD 8} : TD 8 := {}.
Instance Ttb8 `{TD 8} : BD (S 8) := {}.

Instance BtL9 `{BD 9} : LD 9 := {}.
Instance BtR9 `{BD 9} : RD 9 := {}.
Instance LtR9 `{LD 9} : TD 9 := {}.
Instance RtR9 `{RD 9} : TD 9 := {}.
Instance Ttb9 `{TD 9} : BD (S 9) := {}.

Instance BtL10 `{BD 10} : LD 10 := {}.
Instance BtR10 `{BD 10} : RD 10 := {}.
Instance LtR10 `{LD 10} : TD 10 := {}.
Instance RtR10 `{RD 10} : TD 10 := {}.
Instance Ttb10 `{TD 10} : BD (S 10) := {}.

Instance BtL11 `{BD 11} : LD 11 := {}.
Instance BtR11 `{BD 11} : RD 11 := {}.
Instance LtR11 `{LD 11} : TD 11 := {}.
Instance RtR11 `{RD 11} : TD 11 := {}.
Instance Ttb11 `{TD 11} : BD (S 11) := {}.

Instance TestTD10 : TD 11 := _.

(* Partial Simple Diamond example *)
Class T (n : nat).
Class R (n : nat).
Class L (n : nat).
Class B (n : nat).
Instance BtL n `{B n} : L n := {}.
Instance BtR n `{B n} : R n := {}.
Instance LtR n `{L n} : T n := {}.
Instance RtR n `{R n} : T n := {}.
Instance Ttb n `{T n} : B (S n) := {}.

Instance B0 : B 0 := {}.

Instance Test0 : B 0 := _.
Instance Test1 : B 1 := _.
Instance Test2 : B 2 := _.

Instance Test10 : B 10 := _.

Instance Test4 : B 4 := _.
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
