  $ . ../setup-project.sh
  $ dune build test.vo 2>&1 | sed 's/T = [0-9]*\.[0-9]*/T = __TIME__/g'
  Query assignments:
    BO = fix `add` 0 
   (prod `n` (global (indt «nat»)) c0 \
     prod `m` (global (indt «nat»)) c1 \ global (indt «nat»)) c0 \
   fun `n` (global (indt «nat»)) c1 \
    fun `m` (global (indt «nat»)) c2 \
     match c1 (fun `n` (global (indt «nat»)) c3 \ global (indt «nat»)) 
      [c2, 
       fun `p` (global (indt «nat»)) c3 \
        app [global (indc «S»), app [c0, c3, c2]]]
    GR = «Nat.add»
    GRNat = indt «nat»
    GRSucc = indc «S»
    Nat = global (indt «nat»)
    Succ = global (indc «S»)
    TY = prod `n` (global (indt «nat»)) c0 \
   prod `m` (global (indt «nat»)) c1 \ global (indt «nat»)
  Query assignments:
    GR = «empty_nat»
    TY = global (indt «nat»)
  Query assignments:
    GR1 = indc «Vector.nil»
    GR2 = indt «nat»
    GR3 = const «A»
  add_equal
  Query assignments:
    BO = fix `add` 0 
   (prod `n` (global (indt «nat»)) c0 \
     prod `m` (global (indt «nat»)) c1 \ global (indt «nat»)) c0 \
   fun `n` (global (indt «nat»)) c1 \
    fun `m` (global (indt «nat»)) c2 \
     match c1 (fun `n` (global (indt «nat»)) c3 \ global (indt «nat»)) 
      [c2, 
       fun `p` (global (indt «nat»)) c3 \
        app [global (indc «S»), app [c0, c3, c2]]]
    GR = «Nat.add»
    NGR = «add_equal»
    Name = add_equal
    S = add
    Spilled_1 = add_equal
    Spilled_2 = add_equal
    TY = prod `n` (global (indt «nat»)) c0 \
   prod `m` (global (indt «nat»)) c1 \ global (indt «nat»)
  add_equal : nat -> nat -> nat
  
  add_equal is not universe polymorphic
  Arguments add_equal (n m)%nat_scope
  add_equal is opaque
  Expands to: Constant test.test.add_equal
  «myfalse»
  Query assignments:
    F = indt «False»
    GR = «myfalse»
  myfalse
       : False
  parameter T X0 (sort (typ X1)) c0 \
   record eq_class (sort (typ X2)) mk_eq_class 
    (field [canonical ff, coercion regular] eq_f (global (indt «bool»)) c1 \
      field X3 eq_proof 
       (app [global (indt «eq»), global (indt «bool»), c1, c1]) c2 \
       end-record)
  Query assignments:
    DECL = parameter T X0 (sort (typ «eq_class.u0»)) c0 \
   record eq_class (sort (typ «eq_class.u1»)) mk_eq_class 
    (field [canonical ff, coercion regular] eq_f (global (indt «bool»)) c1 \
      field X3 eq_proof 
       (app [global (indt «eq»), global (indt «bool»), c1, c1]) c2 \
       end-record)
    GR = «eq_class»
    _uvk_1_ = «eq_class.u0»
    _uvk_2_ = «eq_class.u1»
  Universe constraints:
  UNIVERSES:
   
  ALGEBRAIC UNIVERSES:
   {eq_class.u1 eq_class.u0}
  FLEXIBLE UNIVERSES:
   eq_class.u1
   eq_class.u0
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Record eq_class (T : Type@{eq_class.u0}) : Type@{eq_class.u1} := mk_eq_class
    { eq_f : bool;  eq_proof : eq_f = eq_f }.
  
  Arguments eq_class T%type_scope
  Arguments mk_eq_class T%type_scope eq_f%bool_scope eq_proof
  fun x : eq_class nat => x : bool
       : eq_class nat -> bool
  p <- eq_proof ( xxx )
  Query assignments:
    DECL = parameter T X0 (sort (typ «prim_eq_class.u0»)) c0 \
   record prim_eq_class (sort (typ «prim_eq_class.u1»)) mk_prim_eq_class 
    (field [canonical ff, coercion reversible] prim_eq_f 
      (global (indt «bool»)) c1 \
      field X1 prim_eq_proof 
       (app [global (indt «eq»), global (indt «bool»), c1, c1]) c2 \
       end-record)
    GR = «prim_eq_class»
    _uvk_3_ = «prim_eq_class.u0»
    _uvk_4_ = «prim_eq_class.u1»
  Universe constraints:
  UNIVERSES:
   
  ALGEBRAIC UNIVERSES:
   {prim_eq_class.u1 prim_eq_class.u0}
  FLEXIBLE UNIVERSES:
   prim_eq_class.u1
   prim_eq_class.u0
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  fun r : prim_eq_class nat =>
  eq_refl : r = {| prim_eq_f := r; prim_eq_proof := prim_eq_proof _ r |}
       : forall r : prim_eq_class nat,
         r = {| prim_eq_f := r; prim_eq_proof := prim_eq_proof _ r |}
  (* {} |= prim_eq_class.u1 <= eq.u0 *)
  fun `r` (app [global (indt «prim_eq_class»), global (indt «nat»)]) c0 \
   app [primitive (proj test.test.prim_eq_f 1), c0]
  Query assignments:
    C = «pc»
  Universe constraints:
  UNIVERSES:
   
  ALGEBRAIC UNIVERSES:
   {myind.u0}
  FLEXIBLE UNIVERSES:
   myind.u0
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  myind true false : Prop
       : Prop
  K2 true : myind true true
       : myind true true
  myind1 true false : Prop
       : Prop
  K21 true : myind1 true true
       : myind1 true true
  Query assignments:
    _uvk_6_ = «nuind.u0»
    _uvk_7_ = «nuind.u1»
  Universe constraints:
  UNIVERSES:
   
  ALGEBRAIC UNIVERSES:
   {nuind.u1 nuind.u0}
  FLEXIBLE UNIVERSES:
   nuind.u1
   nuind.u0
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  fun x : nuind nat 3 false =>
  match x in (nuind _ _ b) return (b = b) with
  | k1 _ _ => eq_refl : true = true
  | k2 _ _ x0 => (fun _ : nuind nat 1 false => eq_refl : false = false) x0
  end
       : nuind nat 3 false -> false = false
  c0 global (indt «nat»)
  Query assignments:
    T = global (indt «nat»)
  Query assignments:
    D = parameter A X0 (sort (typ «tx.u0»)) c0 \
   inductive tx X1 
    (parameter y X2 (global (indt «nat»)) c1 \
      arity (prod `_` (global (indt «bool»)) c2 \ sort (typ «tx.u1»))) c1 \
    [constructor K1x 
      (parameter y X3 (global (indt «nat»)) c2 \
        arity
         (prod `x` c0 c3 \
           prod `n` (global (indt «nat»)) c4 \
            prod `p` 
             (app
               [global (indt «eq»), global (indt «nat»), 
                app [global (indc «S»), c4], c2]) c5 \
             prod `e` (app [c1, c4, global (indc «true»)]) c6 \
              app [c1, c2, global (indc «true»)])), 
     constructor K2x 
      (parameter y X4 (global (indt «nat»)) c2 \
        arity (app [c1, c2, global (indc «false»)]))]
    _uvk_8_ = «tx.u0»
    _uvk_9_ = «tx.u1»
  Universe constraints:
  UNIVERSES:
   {test.test.18 test.test.17 test.test.16 test.test.15 test.test.14
    test.test.13 test.test.11} |=
     tx.u0 < test.test.11
     tx.u1 < test.test.13
     Set <= eq.u0
     Set <= test.test.13
     Set <= test.test.14
     Set <= test.test.15
     Set <= test.test.16
     Set <= test.test.17
     Set <= test.test.18
     tx.u0 <= test.test.14
     tx.u1 <= test.test.14
     test.test.14 <= tx.u1
  ALGEBRAIC UNIVERSES:
   {tx.u1 tx.u0}
  FLEXIBLE UNIVERSES:
   tx.u1
   tx.u0
  SORTS:
   α2 := Type
   α3 := Type
   α4 := Type
   α5 := Type
  WEAK CONSTRAINTS:
   
  
  Query assignments:
    D = parameter A explicit (sort (typ «test.test.20»)) c0 \
   parameter a explicit c0 c1 \
    inductive ind1 tt 
     (parameter B explicit (sort (typ «ind1.u0»)) c2 \
       parameter b explicit c2 c3 \
        arity
         (prod `C` (sort (typ «test.test.22»)) c4 \
           prod `_` c4 c5 \ sort (typ «test.test.26»))) c2 \
     [constructor k1 
       (parameter B explicit (sort (typ «ind1.u0»)) c3 \
         parameter b explicit c3 c4 \
          arity
           (prod `bb` (app [global (indt «prod»), c3, c3]) c5 \
             prod `_` 
              (app
                [c2, app [global (indt «prod»), c3, c3], c5, 
                 global (indt «bool»), global (indc «true»)]) c6 \
              app [c2, c3, c4, global (indt «unit»), global (indc «tt»)])), 
      constructor k2 
       (parameter B explicit (sort (typ «ind1.u0»)) c3 \
         parameter b explicit c3 c4 \
          arity
           (app
             [c2, c3, c4, global (indt «nat»), 
              app [global (indc «S»), global (indc «O»)]]))]
    D1 = parameter A explicit (sort (typ «test.test.20»)) c0 \
   parameter a explicit c0 c1 \
    inductive ind1 tt 
     (parameter B explicit (sort (typ «ind1.u0»)) c2 \
       parameter b explicit c2 c3 \
        arity
         (prod `C` (sort (typ «test.test.22»)) c4 \
           prod `_` c4 c5 \ sort (typ «test.test.26»))) c2 \
     [constructor k1 
       (parameter B explicit (sort (typ «ind1.u0»)) c3 \
         parameter b explicit c3 c4 \
          arity
           (prod `bb` (app [global (indt «prod»), c3, c3]) c5 \
             prod `_` 
              (app
                [c2, app [global (indt «prod»), c3, c3], c5, 
                 global (indt «bool»), global (indc «true»)]) c6 \
              app [c2, c3, c4, global (indt «unit»), global (indc «tt»)])), 
      constructor k2 
       (parameter B explicit (sort (typ «ind1.u0»)) c3 \
         parameter b explicit c3 c4 \
          arity
           (app
             [c2, c3, c4, global (indt «nat»), 
              app [global (indc «S»), global (indc «O»)]]))]
    I = «ind1»
    U = «test.test.26»
    UA = «test.test.20»
    UB1 = «ind1.u0»
    UB2 = «ind1.u0»
    UB3 = «ind1.u0»
    UC = «test.test.22»
  Universe constraints:
  UNIVERSES:
   {test.test.26} |= Set <= test.test.26
                     ind1.u0 <= test.test.26
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Query assignments:
    D = parameter A explicit (sort (typ «test.test.20»)) c0 \
   parameter a explicit c0 c1 \
    inductive ind1 tt 
     (parameter B explicit (sort (typ «ind1.u0»)) c2 \
       parameter b explicit c2 c3 \
        arity
         (prod `C` (sort (typ «test.test.22»)) c4 \
           prod `_` c4 c5 \ sort (typ «test.test.27»))) c2 \
     [constructor k1 
       (parameter B explicit (sort (typ «ind1.u0»)) c3 \
         parameter b explicit c3 c4 \
          parameter bb implicit (app [global (indt «prod»), c3, c3]) c5 \
           arity
            (prod `_` 
              (app
                [c2, app [global (indt «prod»), c3, c3], c5, 
                 global (indt «bool»), global (indc «true»)]) c6 \
              app [c2, c3, c4, global (indt «unit»), global (indc «tt»)])), 
      constructor k2 
       (parameter B explicit (sort (typ «ind1.u0»)) c3 \
         parameter b explicit c3 c4 \
          arity
           (app
             [c2, c3, c4, global (indt «nat»), 
              app [global (indc «S»), global (indc «O»)]]))]
    D1 = parameter A explicit (sort (typ «test.test.20»)) c0 \
   parameter a explicit c0 c1 \
    inductive ind1 tt 
     (parameter B explicit (sort (typ «ind1.u0»)) c2 \
       parameter b explicit c2 c3 \
        arity
         (prod `C` (sort (typ «test.test.22»)) c4 \
           prod `_` c4 c5 \ sort (typ «test.test.27»))) c2 \
     [constructor k1 
       (parameter B explicit (sort (typ «ind1.u0»)) c3 \
         parameter b explicit c3 c4 \
          parameter bb implicit (app [global (indt «prod»), c3, c3]) c5 \
           arity
            (prod `_` 
              (app
                [c2, app [global (indt «prod»), c3, c3], c5, 
                 global (indt «bool»), global (indc «true»)]) c6 \
              app [c2, c3, c4, global (indt «unit»), global (indc «tt»)])), 
      constructor k2 
       (parameter B explicit (sort (typ «ind1.u0»)) c3 \
         parameter b explicit c3 c4 \
          arity
           (app
             [c2, c3, c4, global (indt «nat»), 
              app [global (indc «S»), global (indc «O»)]]))]
    I = «ind1»
    U = «test.test.27»
    UA = «test.test.20»
    UB1 = «ind1.u0»
    UB2 = «ind1.u0»
    UB3 = «ind1.u0»
    UC = «test.test.22»
  Universe constraints:
  UNIVERSES:
   {test.test.27} |= Set <= test.test.27
                     ind1.u0 <= test.test.27
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Query assignments:
    D = parameter P explicit (sort (typ «r1.u0»)) c0 \
   parameter p explicit c0 c1 \
    record r1 (sort (typ «r1.u0»)) mk_r1 
     (field [coercion reversible, canonical tt] f1 (prod `_` c0 c2 \ c0) c2 \
       field [coercion off, canonical ff] f2 
        (app [global (indt «eq»), c0, c1, app [c2, c1]]) c3 \ end-record)
    D1 = parameter P explicit (sort (typ «r1.u0»)) c0 \
   parameter p explicit c0 c1 \
    record r1 (sort (typ «r1.u0»)) mk_r1 
     (field [coercion reversible, canonical tt] f1 (prod `_` c0 c2 \ c0) c2 \
       field [coercion off, canonical ff] f2 
        (app [global (indt «eq»), c0, c1, app [c2, c1]]) c3 \ end-record)
    I = «r1»
    UP = «r1.u0»
    UR = «r1.u0»
  Query assignments:
    D = parameter P explicit (sort (typ «r1.u0»)) c0 \
   parameter p explicit c0 c1 \
    record r1 (sort (typ «r1.u0»)) mk_r1 
     (field [coercion reversible, canonical tt] f1 (prod `_` c0 c2 \ c0) c2 \
       field [coercion regular, canonical ff] f2 
        (app [global (indt «eq»), c0, c1, app [c2, c1]]) c3 \ end-record)
    D1 = parameter P explicit (sort (typ «r1.u0»)) c0 \
   parameter p explicit c0 c1 \
    record r1 (sort (typ «r1.u0»)) mk_r1 
     (field [coercion reversible, canonical tt] f1 (prod `_` c0 c2 \ c0) c2 \
       field [coercion regular, canonical ff] f2 
        (app [global (indt «eq»), c0, c1, app [c2, c1]]) c3 \ end-record)
    I = «r1»
    UP = «r1.u0»
    UR = «r1.u0»
  {{ nat; S;  }}
  {{ nat; S;  }}
  Query assignments:
    GR = const «Nat.add»
    L = {{ nat; S;  }}
    S = {{ nat; S;  }}
  {{ X.a;  }} {{ X.a; Nat.add; nat;  }}
  {{ X.a;  }} {{ X.a; Nat.add; nat; O; S;  }}
  Query assignments:
    AllL = {{ X.a; Nat.add; nat;  }}
    AllS = {{ X.a; Nat.add; nat; O; S;  }}
    GR = const «X.b»
    L = {{ X.a;  }}
    M = «test.test.HOAS.X»
    S = {{ X.a;  }}
    Spilled_1 = const «X.a»
  Query assignments:
    GR = const «Ranalysis5.derivable_pt_lim_CVU»
    S = {{ Field_theory.AF_1_neq_0; Field_theory.AF_AR; Field_theory.AFdiv_def;
       Field_theory.AFinv_l; Ring_theory.ARadd_0_l; Ring_theory.ARadd_0_r;
       Ring_theory.ARadd_assoc; Ring_theory.ARadd_assoc1;
       Ring_theory.ARadd_assoc2; Ring_theory.ARadd_comm; Ring_theory.ARdistr_l;
       Ring_theory.ARdistr_r; InitialRing.ARgen_phiPOS_Psucc;
       InitialRing.ARgen_phiPOS_add; InitialRing.ARgen_phiPOS_mult;
       Ring_theory.ARmul_0_l; Ring_theory.ARmul_0_r; Ring_theory.ARmul_1_l;
       Ring_theory.ARmul_1_r; Ring_theory.ARmul_assoc;
       Ring_theory.ARmul_assoc1; Ring_theory.ARmul_assoc2;
       Ring_theory.ARmul_comm; Ring_theory.ARopp_add; Ring_theory.ARopp_mul_l;
       Ring_theory.ARopp_mul_r; Ring_theory.ARopp_zero; Ring_theory.ARsub_def;
       Ring_theory.ARsub_ext; Ring_theory.ARth_SRth; RList.AbsList;
       RList.AbsList_P1; RList.AbsList_P2; Acc_inv;
       Morphisms_Prop.Acc_pt_morphism; Acc_rect; Tauto.BFormula;
       PSeries_reg.Ball_in_inter; Rlimit.Base; PSeries_reg.Boule;
       PSeries_reg.Boule_center; Setoid.Build_Setoid_Theory;
       Ring_polynom.CFactor; RMicromega.CInvR0; RMicromega.CPowR0;
       ConstructiveReals.CR_Q_dense; ConstructiveReals.CR_archimedean;
       ConstructiveReals.CR_cauchy; ConstructiveReals.CR_complete;
       ConstructiveReals.CR_cv; ConstructiveLimits.CR_cv_bound_down;
       ConstructiveLimits.CR_cv_le; ConstructiveLimits.CR_cv_open_above;
       ConstructiveLimits.CR_cv_open_below; ConstructiveLimits.CR_cv_opp;
       ConstructiveLimits.CR_cv_plus; ConstructiveLimits.CR_cv_proper;
       ConstructiveReals.CR_of_Q; ConstructiveReals.CR_of_Q_le;
       ConstructiveReals.CR_of_Q_lt; ConstructiveReals.CR_of_Q_morph;
       ConstructiveReals.CR_of_Q_morph_Proper;
       ConstructiveReals.CR_of_Q_morph_T; ConstructiveReals.CR_of_Q_mult;
       ConstructiveReals.CR_of_Q_opp; ConstructiveReals.CR_of_Q_plus;
       ConstructiveReals.CR_of_Q_pos; ConstructiveLUB.CR_sig_lub;
       ConstructiveReals.CRabs; ConstructiveReals.CRabs_def;
       ConstructiveAbs.CRabs_le; ConstructiveAbs.CRabs_lt;
       ConstructiveAbs.CRabs_morph; ConstructiveAbs.CRabs_morph_prop_Proper;
       ConstructiveAbs.CRabs_opp; ConstructiveAbs.CRabs_right;
       ConstructiveAbs.CRabs_triang; ConstructiveReals.CRapart;
       ConstructiveReals.CRcarrier; ConstructiveRcomplete.CRealAbsLUB;
       ConstructiveCauchyRealsMult.CRealArchimedean;
       ConstructiveRcomplete.CRealComplete;
       ConstructiveRcomplete.CRealConstructive;
       ConstructiveCauchyReals.CRealEq; ConstructiveCauchyReals.CRealEq_diff;
       ConstructiveCauchyReals.CRealEq_refl;
       ConstructiveCauchyReals.CRealEq_rel;
       ConstructiveCauchyReals.CRealEq_relT;
       ConstructiveCauchyReals.CRealEq_rel_Reflexive;
       ConstructiveCauchyReals.CRealEq_rel_Symmetric;
       ConstructiveCauchyReals.CRealEq_rel_Transitive;
       ConstructiveCauchyReals.CRealEq_sym;
       ConstructiveCauchyReals.CRealEq_trans; ConstructiveCauchyReals.CRealGe;
       ConstructiveCauchyReals.CRealLe;
       ConstructiveCauchyAbs.CRealLe_0R_to_single_dist;
       ConstructiveCauchyReals.CRealLe_morph_Proper;
       ConstructiveCauchyReals.CRealLe_not_lt;
       ConstructiveCauchyReals.CRealLe_refl;
       ConstructiveCauchyRealsMult.CRealLowerBound;
       ConstructiveCauchyRealsMult.CRealLowerBoundSpec;
       ConstructiveCauchyRealsMult.CRealLowerBound_lt_scale;
       ConstructiveCauchyReals.CRealLt;
       ConstructiveRcomplete.CRealLtDisjunctEpsilon;
       ConstructiveCauchyReals.CRealLtEpsilon;
       ConstructiveCauchyReals.CRealLtForget;
       ConstructiveRcomplete.CRealLtIsLinear;
       ConstructiveCauchyReals.CRealLtProp;
       ConstructiveCauchyReals.CRealLtProp_morph_Proper;
       ConstructiveCauchyReals.CRealLt_0_1;
       ConstructiveCauchyAbs.CRealLt_RQ_from_single_dist;
       ConstructiveCauchyReals.CRealLt_above;
       ConstructiveCauchyReals.CRealLt_aboveSig;
       ConstructiveCauchyReals.CRealLt_aboveSig';
       ConstructiveCauchyReals.CRealLt_above_same;
       ConstructiveCauchyReals.CRealLt_asym;
       ConstructiveCauchyReals.CRealLt_dec;
       ConstructiveCauchyReals.CRealLt_irrefl;
       ConstructiveCauchyReals.CRealLt_lpo_dec;
       ConstructiveCauchyReals.CRealLt_morph;
       ConstructiveCauchyRealsMult.CRealQ_dense;
       ConstructiveCauchyRealsMult.CRealRing_ring_lemma1;
       ConstructiveCauchyRealsMult.CRealRing_ring_lemma2;
       ConstructiveCauchyAbs.CReal_abs;
       ConstructiveCauchyAbs.CReal_abs_appart_0;
       ConstructiveCauchyAbs.CReal_abs_bound;
       ConstructiveCauchyAbs.CReal_abs_cauchy;
       ConstructiveCauchyAbs.CReal_abs_def2;
       ConstructiveCauchyAbs.CReal_abs_le;
       ConstructiveCauchyAbs.CReal_abs_left;
       ConstructiveCauchyAbs.CReal_abs_minus_sym;
       ConstructiveCauchyAbs.CReal_abs_morph;
       ConstructiveCauchyAbs.CReal_abs_morph_Proper;
       ConstructiveCauchyAbs.CReal_abs_opp;
       ConstructiveCauchyAbs.CReal_abs_pos;
       ConstructiveCauchyAbs.CReal_abs_right;
       ConstructiveCauchyAbs.CReal_abs_scale;
       ConstructiveCauchyAbs.CReal_abs_seq;
       ConstructiveCauchyAbs.CReal_abs_triang;
       ConstructiveCauchyReals.CReal_appart;
       ConstructiveRcomplete.CReal_cv_self';
       ConstructiveRcomplete.CReal_from_cauchy;
       ConstructiveRcomplete.CReal_from_cauchy_bound;
       ConstructiveRcomplete.CReal_from_cauchy_cauchy;
       ConstructiveRcomplete.CReal_from_cauchy_cm;
       ConstructiveRcomplete.CReal_from_cauchy_cm_mono;
       ConstructiveRcomplete.CReal_from_cauchy_scale;
       ConstructiveRcomplete.CReal_from_cauchy_seq;
       ConstructiveRcomplete.CReal_from_cauchy_seq_bound;
       ConstructiveCauchyRealsMult.CReal_inv;
       ConstructiveCauchyRealsMult.CReal_inv_0_lt_compat;
       ConstructiveCauchyRealsMult.CReal_inv_l;
       ConstructiveCauchyRealsMult.CReal_inv_l_pos;
       ConstructiveCauchyRealsMult.CReal_inv_pos;
       ConstructiveCauchyRealsMult.CReal_inv_pos_bound;
       ConstructiveCauchyRealsMult.CReal_inv_pos_cauchy;
       ConstructiveCauchyRealsMult.CReal_inv_pos_cm;
       ConstructiveCauchyRealsMult.CReal_inv_pos_scale;
       ConstructiveCauchyRealsMult.CReal_inv_pos_seq;
       ConstructiveCauchyRealsMult.CReal_isRing;
       ConstructiveCauchyRealsMult.CReal_isRingExt;
       ConstructiveCauchyAbs.CReal_le_abs;
       ConstructiveCauchyReals.CReal_le_lt_trans;
       ConstructiveCauchyReals.CReal_le_trans;
       ConstructiveCauchyReals.CReal_lt_le_trans;
       ConstructiveCauchyReals.CReal_lt_trans;
       ConstructiveCauchyReals.CReal_minus;
       ConstructiveCauchyRealsMult.CReal_mult;
       ConstructiveCauchyRealsMult.CReal_mult_1_l;
       ConstructiveCauchyRealsMult.CReal_mult_assoc;
       ConstructiveCauchyRealsMult.CReal_mult_bound;
       ConstructiveCauchyRealsMult.CReal_mult_cauchy;
       ConstructiveCauchyRealsMult.CReal_mult_comm;
       ConstructiveCauchyRealsMult.CReal_mult_lt_0_compat;
       ConstructiveCauchyRealsMult.CReal_mult_lt_0_compat_correct;
       ConstructiveCauchyRealsMult.CReal_mult_lt_compat_l;
       ConstructiveCauchyRealsMult.CReal_mult_morph_Proper;
       ConstructiveCauchyRealsMult.CReal_mult_plus_distr_l;
       ConstructiveCauchyRealsMult.CReal_mult_proper_0_l;
       ConstructiveCauchyRealsMult.CReal_mult_proper_l;
       ConstructiveCauchyRealsMult.CReal_mult_scale;
       ConstructiveCauchyRealsMult.CReal_mult_seq;
       ConstructiveCauchyRealsMult.CReal_neg_lt_pos;
       ConstructiveCauchyRealsMult.CReal_neg_lt_pos_subproof;
       ConstructiveCauchyReals.CReal_opp; ConstructiveCauchyReals.CReal_opp_0;
       ConstructiveCauchyReals.CReal_opp_bound;
       ConstructiveCauchyReals.CReal_opp_cauchy;
       ConstructiveCauchyReals.CReal_opp_ge_le_contravar;
       ConstructiveCauchyReals.CReal_opp_involutive;
       ConstructiveCauchyRealsMult.CReal_opp_morph_Proper;
       ConstructiveCauchyRealsMult.CReal_opp_morph_T;
       ConstructiveCauchyRealsMult.CReal_opp_mult_distr_l;
       ConstructiveCauchyRealsMult.CReal_opp_mult_distr_r;
       ConstructiveCauchyReals.CReal_opp_scale;
       ConstructiveCauchyReals.CReal_opp_seq;
       ConstructiveCauchyReals.CReal_plus;
       ConstructiveCauchyReals.CReal_plus_0_l;
       ConstructiveCauchyReals.CReal_plus_0_r;
       ConstructiveCauchyReals.CReal_plus_assoc;
       ConstructiveCauchyReals.CReal_plus_bound;
       ConstructiveCauchyReals.CReal_plus_cauchy;
       ConstructiveCauchyReals.CReal_plus_comm;
       ConstructiveCauchyReals.CReal_plus_eq_reg_l;
       ConstructiveCauchyReals.CReal_plus_le_compat;
       ConstructiveCauchyReals.CReal_plus_le_compat_l;
       ConstructiveCauchyReals.CReal_plus_le_lt_compat;
       ConstructiveCauchyReals.CReal_plus_le_reg_r;
       ConstructiveCauchyReals.CReal_plus_lt_compat_l;
       ConstructiveCauchyReals.CReal_plus_lt_compat_r;
       ConstructiveCauchyReals.CReal_plus_lt_reg_l;
       ConstructiveCauchyReals.CReal_plus_lt_reg_r;
       ConstructiveCauchyReals.CReal_plus_morph;
       ConstructiveCauchyReals.CReal_plus_morph_Proper;
       ConstructiveCauchyReals.CReal_plus_morph_T;
       ConstructiveCauchyReals.CReal_plus_opp_l;
       ConstructiveCauchyReals.CReal_plus_opp_r;
       ConstructiveCauchyReals.CReal_plus_proper_l;
       ConstructiveCauchyReals.CReal_plus_proper_r;
       ConstructiveCauchyReals.CReal_plus_scale;
       ConstructiveCauchyReals.CReal_plus_seq;
       ConstructiveCauchyRealsMult.CReal_red_scale;
       ConstructiveCauchyReals.CReal_red_seq;
       ConstructiveCauchyRealsMult.CReal_scale_sep0_limit;
       ConstructiveReals.CReq; ConstructiveReals.CReq_refl;
       ConstructiveReals.CReq_rel; ConstructiveReals.CReq_relT;
       ConstructiveReals.CReq_rel_Reflexive;
       ConstructiveReals.CReq_rel_Symmetric;
       ConstructiveReals.CReq_rel_Transitive; ConstructiveReals.CReq_sym;
       ConstructiveReals.CReq_trans; ConstructiveReals.CRinv;
       ConstructiveReals.CRinv_0_lt_compat; ConstructiveReals.CRinv_l;
       ConstructiveReals.CRinv_r; ConstructiveReals.CRisRing;
       ConstructiveReals.CRisRingExt; ConstructiveLUB.CRis_upper_bound;
       ConstructiveReals.CRle; ConstructiveAbs.CRle_abs;
       ConstructiveReals.CRle_lt_trans; ConstructiveReals.CRle_morph_Proper;
       ConstructiveReals.CRle_refl; ConstructiveReals.CRle_trans;
       ConstructiveReals.CRlt; ConstructiveReals.CRltEpsilon;
       ConstructiveReals.CRltForget; ConstructiveReals.CRltLinear;
       ConstructiveReals.CRltProp; ConstructiveReals.CRlt_asym;
       ConstructiveReals.CRlt_le_trans; ConstructiveLUB.CRlt_lpo_dec;
       ConstructiveReals.CRlt_minus; ConstructiveReals.CRlt_morph;
       ConstructiveReals.CRlt_proper; ConstructiveReals.CRlt_trans;
       ConstructiveReals.CRminus; ConstructiveReals.CRmult;
       ConstructiveReals.CRmult_0_r; ConstructiveReals.CRmult_1_l;
       ConstructiveReals.CRmult_1_r; ConstructiveReals.CRmult_assoc;
       ConstructiveReals.CRmult_comm; ConstructiveReals.CRmult_lt_0_compat;
       ConstructiveReals.CRmult_lt_compat_l;
       ConstructiveReals.CRmult_lt_compat_r; ConstructiveReals.CRmult_lt_reg_l;
       ConstructiveReals.CRmult_lt_reg_r; ConstructiveReals.CRmult_morph;
       ConstructiveReals.CRmult_morph_Proper; ConstructiveReals.CRmult_morph_T;
       ConstructiveReals.CRmult_plus_distr_l;
       ConstructiveReals.CRmult_plus_distr_r; ConstructiveReals.CRopp;
       ConstructiveReals.CRopp_0; ConstructiveReals.CRopp_ge_le_contravar;
       ConstructiveReals.CRopp_gt_lt_contravar;
       ConstructiveReals.CRopp_involutive; ConstructiveReals.CRopp_lt_cancel;
       ConstructiveReals.CRopp_morph_Proper;
       ConstructiveReals.CRopp_mult_distr_l;
       ConstructiveReals.CRopp_mult_distr_r;
       ConstructiveReals.CRopp_plus_distr; ConstructiveReals.CRplus;
       ConstructiveReals.CRplus_0_l; ConstructiveReals.CRplus_0_r;
       ConstructiveReals.CRplus_assoc; ConstructiveReals.CRplus_comm;
       ConstructiveReals.CRplus_eq_reg_l; ConstructiveReals.CRplus_le_compat;
       ConstructiveReals.CRplus_le_compat_l;
       ConstructiveReals.CRplus_le_compat_r; ConstructiveReals.CRplus_le_reg_l;
       ConstructiveReals.CRplus_le_reg_r; ConstructiveReals.CRplus_lt_compat_l;
       ConstructiveReals.CRplus_lt_compat_r; ConstructiveReals.CRplus_lt_reg_l;
       ConstructiveReals.CRplus_lt_reg_r; ConstructiveReals.CRplus_morph;
       ConstructiveReals.CRplus_morph_Proper; ConstructiveReals.CRplus_morph_T;
       ConstructiveReals.CRplus_opp_l; ConstructiveReals.CRplus_opp_r;
       ConstructiveReals.CRup_nat; ConstructiveReals.CRzero_double;
       PSeries_reg.CVU; CompOpp; CompOpp_iff; CompOpp_inj; CompOpp_involutive;
       CompSpec; CompSpec2Type; CompSpecT; CompareSpec2Type;
       ConstructiveLUB.DDcut_limit; ConstructiveLUB.DDcut_limit_fix;
       ConstructiveLUB.DDdec; ConstructiveLUB.DDhigh;
       ConstructiveLUB.DDhighProp; ConstructiveLUB.DDinterval;
       ConstructiveLUB.DDlow; ConstructiveLUB.DDlowProp;
       ConstructiveLUB.DDlow_below_up; ConstructiveLUB.DDproper;
       ConstructiveLUB.DDupcut; Rderiv.D_in; Rderiv.D_x; Rderiv.Dmult; Env.Env;
       Ring_theory.Eq_ext; Ring_theory.Eqsth; RelationClasses.Equivalence_PER;
       CRelationClasses.Equivalence_Reflexive;
       RelationClasses.Equivalence_Reflexive;
       CRelationClasses.Equivalence_Symmetric;
       RelationClasses.Equivalence_Symmetric;
       RelationClasses.Equivalence_Transitive; ZMicromega.F; Field_theory.F2AF;
       Field_theory.FEeval; Field_theory.FExpr_ind; Field_theory.F_1_neq_0;
       Field_theory.F_R; False_ind; False_rec; False_rect; Field_theory.Fapp;
       Field_theory.Fcons0; Field_theory.Fcons1; Field_theory.Fcons2;
       Field_theory.Fdiv_def; Field_theory.Field_correct;
       Field_theory.Field_rw_pow_correct;
       Field_theory.Field_simplify_eq_pow_correct; Field_theory.Finv_l;
       Field_theory.Fnorm; Field_theory.Fnorm_FEeval_PEeval;
       Field_theory.Fnorm_crossproduct; Tauto.GFormula_ind; ID;
       Ring_theory.IDmorph; Ring_theory.IDphi; Rdefinitions.IPR;
       Rdefinitions.IPR_2; RIneq.IPR_2_xH; RIneq.IPR_2_xI; RIneq.IPR_2_xO;
       RIneq.IPR_IPR_2; RIneq.IPR_ge_1; RIneq.IPR_gt_0; RIneq.IPR_xH;
       RIneq.IPR_xI; RIneq.IPR_xO; Rdefinitions.IZR; RIneq.IZR_ge;
       RIneq.IZR_le; RIneq.IZR_lt; Qreals.IZR_nz; List.In; ZifyInst.Inj_Z_Z;
       ZifyInst.Inj_pos_Z; RelationClasses.Irreflexive; Ring_polynom.MFactor;
       Ring_polynom.MPcond; MVT.MVT; RList.MaxRlist; RList.MaxRlist_P1;
       Ring_polynom.Mcphi_ok; RList.MinRlist; RList.MinRlist_P1;
       RList.MinRlist_P2; Ring_polynom.Mphi; Ring_polynom.Mphi_ok;
       RingMicromega.NFormula; Classical_Prop.NNPP; Field_theory.NPEadd;
       Field_theory.NPEadd_ok; Field_theory.NPEequiv; Field_theory.NPEequiv_eq;
       Field_theory.NPEeval_ext; Field_theory.NPEmul; Field_theory.NPEmul_ok;
       Field_theory.NPEopp; Field_theory.NPEopp_ok; Field_theory.NPEpow;
       Field_theory.NPEpow_ok; Field_theory.NPEsub; Field_theory.NPEsub_ok;
       InitialRing.Nopp; InitialRing.Nsub; Field_theory.NtoZ;
       InitialRing.Ntriv_div_th; O_S; ConstructiveEpsilon.O_witness;
       RingMicromega.OpAdd; RingMicromega.OpAdd_sound; RingMicromega.OpMult;
       RingMicromega.OpMult_sound; ConstructiveEpsilon.P';
       ConstructiveEpsilon.P'_decidable; EnvRing.P0; Ring_polynom.P0;
       EnvRing.P1; Ring_polynom.P1; Field_theory.PCond; Field_theory.PCond_app;
       Field_theory.PCond_cons; RelationClasses.PER_Symmetric;
       RelationClasses.PER_Transitive; Morphisms.PER_morphism;
       Morphisms.PER_morphism_obligation_1; Field_theory.PE_1_l;
       Field_theory.PE_1_r; Field_theory.PEadd_ext; EnvRing.PEeval;
       Ring_polynom.PEeval; Field_theory.PEmul_ext; Field_theory.PEopp_ext;
       Field_theory.PEpow_0_r; Field_theory.PEpow_1_l; Field_theory.PEpow_1_r;
       Field_theory.PEpow_add_r; Field_theory.PEpow_ext;
       Field_theory.PEpow_mul_l; Field_theory.PEpow_mul_r;
       Field_theory.PEpow_nz; Field_theory.PEsimp; Field_theory.PEsimp_ok;
       Field_theory.PEsub_ext; Field_theory.PExpr_eq;
       Field_theory.PExpr_eq_semi_ok; Field_theory.PExpr_eq_spec;
       EnvRing.PExpr_ind; Ring_polynom.PExpr_ind;
       Field_theory.PFcons0_fcons_inv; Field_theory.PFcons1_fcons_inv;
       Field_theory.PFcons2_fcons_inv; Ring_polynom.PNSubst;
       Ring_polynom.PNSubst1; Ring_polynom.PNSubst1_ok; Ring_polynom.PNSubstL;
       Ring_polynom.PNSubstL_ok; Ring_polynom.PNSubst_ok;
       Ring_polynom.POneSubst; Ring_polynom.POneSubst_ok; Ring_polynom.PSubstL;
       Ring_polynom.PSubstL1; Ring_polynom.PSubstL1_ok;
       Ring_polynom.PSubstL_ok; Ring_polynom.PX_ext; EnvRing.Padd;
       Ring_polynom.Padd; EnvRing.PaddC; Ring_polynom.PaddC; EnvRing.PaddC_ok;
       Ring_polynom.PaddC_ok; EnvRing.PaddI; Ring_polynom.PaddI; EnvRing.PaddX;
       Ring_polynom.PaddX; EnvRing.PaddX_ok; Ring_polynom.PaddX_ok;
       EnvRing.Padd_ok; Ring_polynom.Padd_ok; Field_theory.Pcond_Fnorm;
       Field_theory.Pcond_simpl_complete; EnvRing.Peq; Ring_polynom.Peq;
       EnvRing.Peq_ok; Ring_polynom.Peq_ok; EnvRing.Peq_spec;
       Ring_polynom.Peq_spec; Ring_polynom.Pequiv; Ring_polynom.Pequiv_eq;
       EnvRing.Pjump_add; EnvRing.Pjump_pred_double; EnvRing.Pjump_xO_tail;
       EnvRing.Pmul; Ring_polynom.Pmul; EnvRing.PmulC; Ring_polynom.PmulC;
       EnvRing.PmulC_aux; Ring_polynom.PmulC_aux; EnvRing.PmulC_aux_ok;
       Ring_polynom.PmulC_aux_ok; EnvRing.PmulC_ok; Ring_polynom.PmulC_ok;
       EnvRing.PmulI; Ring_polynom.PmulI; EnvRing.PmulI_ok;
       Ring_polynom.PmulI_ok; EnvRing.Pmul_ok; Ring_polynom.Pmul_ok;
       RingMicromega.PolC; RingMicromega.PolEnv; EnvRing.Pol_ind;
       Ring_polynom.Pol_ind; EnvRing.Popp; Ring_polynom.Popp; EnvRing.Popp_ok;
       Ring_polynom.Popp_ok; ConstructiveRcomplete.Pos2Z_pos_is_pos;
       QExtra.Pos_log2floor_plus1; QExtra.Pos_log2floor_plus1_spec;
       PosExtra.Pos_pow_1_r; PosExtra.Pos_pow_le_mono_r;
       ConstructiveExtra.Pos_pred_double_inj;
       ConstructiveRcomplete.Pospow_lin_le_2pow; EnvRing.Pphi;
       Ring_polynom.Pphi; EnvRing.Pphi0; Ring_polynom.Pphi0; EnvRing.Pphi1;
       Ring_polynom.Pphi1; Ring_polynom.Pphi_avoid; Ring_polynom.Pphi_avoid_ok;
       Ring_polynom.Pphi_dev; Ring_polynom.Pphi_dev_ok; Ring_polynom.Pphi_ext;
       Ring_polynom.Pphi_pow; Ring_polynom.Pphi_pow_ok;
       BinPos.Pplus_one_succ_l; BinPos.Pplus_one_succ_r; EnvRing.Ppow_N;
       Ring_polynom.Ppow_N; EnvRing.Ppow_N_ok; Ring_polynom.Ppow_N_ok;
       EnvRing.Ppow_pos; Ring_polynom.Ppow_pos; EnvRing.Ppow_pos_ok;
       Ring_polynom.Ppow_pos_ok; RelationClasses.PreOrder_Reflexive;
       RelationClasses.PreOrder_Transitive; RIneq.Private_sumbool_to_or;
       CMorphisms.Proper; Morphisms.Proper; CMorphisms.ProperProxy;
       Morphisms.ProperProxy; Qminmax.Q.Proper_instance_0;
       BinInt.Z.Proper_instance_0; RingMicromega.Psatz_ind; EnvRing.Psquare;
       EnvRing.Psquare_ok; EnvRing.Psub; Ring_polynom.Psub; EnvRing.PsubC;
       Ring_polynom.PsubC; EnvRing.PsubC_ok; RingMicromega.PsubC_ok;
       Ring_polynom.PsubC_ok; EnvRing.PsubI; Ring_polynom.PsubI; EnvRing.PsubX;
       Ring_polynom.PsubX; EnvRing.PsubX_ok; EnvRing.Psub_ok;
       Ring_polynom.Psub_ok; Ring_polynom.Psub_opp; Rdefinitions.Q2R;
       RMicromega.Q2R_0; RMicromega.Q2R_1; Qreals.Q2R_inv;
       RMicromega.Q2R_inv_ext; RMicromega.Q2R_m_Proper; Qreals.Q2R_minus;
       Qreals.Q2R_mult; Qreals.Q2R_opp; Qreals.Q2R_plus; RMicromega.Q2R_pow_N;
       RMicromega.Q2R_pow_pos; RMicromega.Q2RpowerRZ;
       ConstructiveCauchyReals.QBound; ConstructiveCauchyReals.QCauchySeq;
       QMicromega.QNpower; RMicromega.QReval_expr; RMicromega.QReval_formula;
       RMicromega.QReval_formula'; RMicromega.QReval_formula_compat;
       QMicromega.QSORaddon; RMicromega.QSORaddon; QMicromega.QTautoChecker;
       QMicromega.QTautoChecker_sound; QMicromega.QWeakChecker;
       QMicromega.QWeakChecker_sound; QMicromega.QWitness;
       QArith_base.Q_Setoid; QArith_base.Q_dec; RMicromega.Q_of_Rcst;
       RMicromega.Q_of_RcstR; Qabs.Qabs;
       ConstructiveRcomplete.Qabs_Qgt_condition; Qabs.Qabs_Qinv;
       Qabs.Qabs_Qle_condition; Qabs.Qabs_Qlt_condition; Qabs.Qabs_Qmult;
       ConstructiveRcomplete.Qabs_Rabs; Qabs.Qabs_case;
       Qabs.Qabs_case_subproof; Qabs.Qabs_case_subproof0;
       Qabs.Qabs_case_subproof1; Qabs.Qabs_gt;
       ConstructiveCauchyAbs.Qabs_involutive; Qabs.Qabs_neg; Qabs.Qabs_nonneg;
       Qabs.Qabs_opp; Qabs.Qabs_pos; Qabs.Qabs_triangle;
       Qabs.Qabs_triangle_reverse; Qabs.Qabs_wd; Qabs.Qabs_wd_Proper;
       QArith_base.Qarchimedean; QExtra.QarchimedeanExp2_Z;
       QExtra.QarchimedeanLowExp2_Z; QExtra.Qbound_lt_ZExp2;
       QExtra.Qbound_lt_ZExp2_spec; QExtra.Qbound_ltabs_ZExp2;
       QExtra.Qbound_ltabs_ZExp2_spec; QArith_base.Qcompare;
       QArith_base.Qcompare_comp; QArith_base.Qden; QArith_base.Qdiv;
       QArith_base.Qdiv_comp; QArith_base.Qdiv_mult_l; QArith_base.Qeq;
       QArith_base.Qeq_alt; QArith_base.Qeq_bool; QArith_base.Qeq_bool_eq;
       QArith_base.Qeq_bool_iff; QArith_base.Qeq_bool_neq; QArith_base.Qeq_dec;
       Qreals.Qeq_eqR; QArith_base.Qeq_eq_bool; RMicromega.Qeq_false;
       QArith_base.Qeq_refl; QArith_base.Qeq_sym; QArith_base.Qeq_trans;
       RMicromega.Qeq_true; QMicromega.Qeval_bop2; QMicromega.Qeval_expr;
       QMicromega.Qeval_expr'; QMicromega.Qeval_expr_compat;
       QMicromega.Qeval_formula; QMicromega.Qeval_formula';
       QMicromega.Qeval_formula_compat; QMicromega.Qeval_nformula;
       RMicromega.Qeval_nformula; QMicromega.Qeval_nformula_dec;
       QMicromega.Qeval_op2; QMicromega.Qeval_op2_hold; QMicromega.Qeval_pop2;
       Qfield.Qfield_field_lemma1; Qfield.Qfield_field_lemma2;
       Qfield.Qfield_lemma5; Qfield.Qfield_ring_lemma1;
       Qfield.Qfield_ring_lemma2; Qround.Qfloor; Qround.Qfloor_le;
       QArith_base.Qinv; QArith_base.Qinv_comp; QArith_base.Qinv_involutive;
       QArith_base.Qinv_le_0_compat; QArith_base.Qinv_lt_0_compat;
       QArith_base.Qinv_lt_contravar; QArith_base.Qinv_mult_distr;
       QArith_base.Qinv_plus_distr; QArith_base.Qinv_pos; Qpower.Qinv_power;
       Qpower.Qinv_power_positive; QArith_base.Qle; Qabs.Qle_Qabs;
       Qreals.Qle_Rle; QArith_base.Qle_alt; QArith_base.Qle_antisym;
       QArith_base.Qle_bool; QArith_base.Qle_bool_iff;
       QArith_base.Qle_bool_imp_le; QArith_base.Qle_comp;
       QArith_base.Qle_lt_trans; QArith_base.Qle_minus_iff;
       QArith_base.Qle_not_lt; QArith_base.Qle_refl;
       QArith_base.Qle_shift_div_l; QArith_base.Qle_shift_div_r;
       QArith_base.Qle_trans; RMicromega.Qle_true;
       QExtra.Qlowbound_lt_ZExp2_spec; QExtra.Qlowbound_ltabs_ZExp2;
       QExtra.Qlowbound_ltabs_ZExp2_inv; QArith_base.Qlt; QArith_base.Qlt_alt;
       QMicromega.Qlt_bool; QMicromega.Qlt_bool_iff; QArith_base.Qlt_compat;
       Qround.Qlt_floor; QArith_base.Qlt_irrefl; QArith_base.Qlt_le_dec;
       QArith_base.Qlt_le_trans; QArith_base.Qlt_le_weak;
       QArith_base.Qlt_leneq; QArith_base.Qlt_minus_iff;
       QArith_base.Qlt_not_eq; QArith_base.Qlt_not_le;
       QArith_base.Qlt_shift_div_l; QArith_base.Qlt_shift_div_r;
       QArith_base.Qlt_shift_inv_l; QArith_base.Qlt_trans;
       ConstructiveRcomplete.Qlt_trans_swap_hyp; QArith_base.Qminus;
       QArith_base.Qminus_comp; QArith_base.Qmult; QArith_base.Qmult_0_l;
       QArith_base.Qmult_0_r; QArith_base.Qmult_1_l; QArith_base.Qmult_1_r;
       QArith_base.Qmult_assoc; QArith_base.Qmult_comm; QArith_base.Qmult_comp;
       QArith_base.Qmult_div_r; QArith_base.Qmult_frac_l;
       QArith_base.Qmult_integral; RMicromega.Qmult_integral;
       QArith_base.Qmult_integral_l; QArith_base.Qmult_inv_r;
       QArith_base.Qmult_le_0_compat; QArith_base.Qmult_le_1_compat;
       QArith_base.Qmult_le_compat_nonneg; QArith_base.Qmult_le_compat_r;
       QArith_base.Qmult_le_l; QArith_base.Qmult_le_lt_compat_pos;
       QArith_base.Qmult_le_r; QArith_base.Qmult_lt_0_le_reg_r;
       QArith_base.Qmult_lt_compat_nonneg; QArith_base.Qmult_lt_compat_r;
       QArith_base.Qmult_lt_l; QArith_base.Qmult_lt_r;
       QArith_base.Qmult_plus_distr_l; QMicromega.Qnegate;
       QMicromega.Qnormalise; QArith_base.Qnot_eq_sym; QArith_base.Qnot_le_lt;
       QArith_base.Qnot_lt_le; QArith_base.Qnum; QArith_base.Qopp;
       QArith_base.Qopp_comp; QArith_base.Qopp_le_compat;
       QArith_base.Qopp_lt_compat; ConstructiveCauchyAbs.Qopp_mult_mone;
       Qfield.Qopp_opp; QArith_base.Qplus; QArith_base.Qplus_0_l;
       QArith_base.Qplus_0_r; QArith_base.Qplus_assoc; QArith_base.Qplus_comm;
       QArith_base.Qplus_comp; QArith_base.Qplus_le_compat;
       QArith_base.Qplus_le_l; QArith_base.Qplus_le_r; QArith_base.Qplus_lt_l;
       QArith_base.Qplus_lt_le_compat; QArith_base.Qplus_lt_r;
       QArith_base.Qplus_opp_r; QArith_base.Qpower; RMicromega.Qpower0;
       Qpower.Qpower_0_le; Qpower.Qpower_0_lt; Qpower.Qpower_0_r;
       Qpower.Qpower_1_le; Qpower.Qpower_1_le_pos;
       ConstructiveRcomplete.Qpower_2powneg_le_inv; QArith_base.Qpower_comp;
       Qpower.Qpower_decomp_pos; Qpower.Qpower_decomp_positive;
       Qpower.Qpower_le_compat_l; Qpower.Qpower_lt_compat_l_inv;
       Qpower.Qpower_minus; Qpower.Qpower_minus_pos;
       Qpower.Qpower_minus_positive; Qpower.Qpower_not_0;
       Qpower.Qpower_not_0_positive; Qpower.Qpower_opp; Qpower.Qpower_plus;
       Qpower.Qpower_plus_positive; Qpower.Qpower_pos_positive;
       QArith_base.Qpower_positive; Qpower.Qpower_positive_0;
       QArith_base.Qpower_positive_comp; RMicromega.Qpower_positive_eq_zero;
       RMicromega.Qpower_positive_zero; Qfield.Qpower_theory; Qreduction.Qred;
       Qreduction.Qred_correct; Qfield.Qsft; QMicromega.Qsor; Qfield.Qsrt;
       Rdefinitions.RbaseSymbolsImpl.R; Rdefinitions.RbaseSymbolsImpl.R0;
       Rdefinitions.RbaseSymbolsImpl.R0_def; Rdefinitions.RbaseSymbolsImpl.R1;
       Rdefinitions.RbaseSymbolsImpl.R1_def; Raxioms.R1_neq_R0;
       RIneq.RField_field_lemma1; RIneq.RField_field_lemma3;
       RIneq.RField_lemma5; RIneq.RField_ring_lemma1; Rbasic_fun.RRle_abs;
       RMicromega.RTautoChecker; RMicromega.RTautoChecker_sound;
       RealField.RTheory; RMicromega.RWeakChecker;
       RMicromega.RWeakChecker_sound; RMicromega.RWitness; Rlimit.R_met;
       RMicromega.R_of_Rcst; RealField.R_power_theory; RIneq.R_rm;
       InitialRing.R_set1; InitialRing.R_set1_Reflexive;
       InitialRing.R_set1_Transitive; InitialRing.R_setoid3;
       InitialRing.R_setoid3_Reflexive; InitialRing.R_setoid3_Symmetric;
       InitialRing.R_setoid3_Transitive; InitialRing.R_setoid4;
       InitialRing.R_setoid4_Reflexive; InitialRing.R_setoid4_Transitive;
       Rbasic_fun.Rabs; Rbasic_fun.Rabs_R0; Rbasic_fun.Rabs_Ropp;
       Rbasic_fun.Rabs_def1; Rbasic_fun.Rabs_def2; Rbasic_fun.Rabs_inv;
       Rbasic_fun.Rabs_minus_sym; Rbasic_fun.Rabs_mult; Rbasic_fun.Rabs_no_R0;
       Rbasic_fun.Rabs_pos; Rbasic_fun.Rabs_pos_eq; Rbasic_fun.Rabs_pos_lt;
       Rbasic_fun.Rabs_right; Rbasic_fun.Rabs_triang;
       Rbasic_fun.Rabs_triang_inv; Rdefinitions.RbaseSymbolsImpl.Rabst;
       Ring_theory.Radd_0_l; Ring_theory.Radd_assoc; Ring_theory.Radd_comm;
       Ring_theory.Radd_ext; Rbasic_fun.Rcase_abs;
       ConstructiveRcomplete.Rcauchy_complete; RMicromega.Rcst_ind;
       RealField.Rdef_pow_add; Rfunctions.Rdist; Rfunctions.Rdist_plus;
       Rfunctions.Rdist_pos; Rfunctions.Rdist_refl; Rfunctions.Rdist_sym;
       Rfunctions.Rdist_tri; Ring_theory.Rdistr_l; Rdefinitions.Rdiv;
       RIneq.Rdiv_plus_distr; CRelationClasses.Reflexive;
       RelationClasses.Reflexive; Morphisms.ReflexiveProxy;
       CMorphisms.Reflexive_partial_app_morphism;
       Morphisms.Reflexive_partial_app_morphism; Rdefinitions.Req_appart_dec;
       RIneq.Req_dec; RIneq.Req_dec_T; OrderedRing.Req_dne; OrderedRing.Req_em;
       RIneq.Req_le; RIneq.Req_le_sym; RMicromega.Reval_bop2;
       RMicromega.Reval_expr; RMicromega.Reval_formula;
       RMicromega.Reval_formula'; RMicromega.Reval_formula_compat;
       RMicromega.Reval_nformula_dec; RMicromega.Reval_op2;
       RMicromega.Reval_op2_hold; RMicromega.Reval_pop2;
       RMicromega.Reval_pop2_eval_op2; RealField.Rfield; Rdefinitions.Rge;
       RIneq.Rge_antisym; RIneq.Rge_gt_dec; RIneq.Rge_gt_trans; RIneq.Rge_le;
       RIneq.Rge_minus; RIneq.Rge_not_lt; RIneq.Rge_trans; Rdefinitions.Rgt;
       RIneq.Rgt_dec; RIneq.Rgt_ge_trans; RIneq.Rgt_lt; RIneq.Rgt_minus;
       RIneq.Rgt_not_eq; RIneq.Rgt_not_ge; RIneq.Rgt_not_le; RIneq.Rgt_trans;
       BinInt.Z.Rgt_wd; Rdefinitions.RinvImpl.Rinv; RIneq.Rinv_0;
       RIneq.Rinv_0_lt_compat; RIneq.Rinv_1; RMicromega.Rinv_1;
       Rdefinitions.RinvImpl.Rinv_def; Raxioms.Rinv_l; RIneq.Rinv_lt_0_compat;
       RIneq.Rinv_mult; RIneq.Rinv_neq_0_compat; RIneq.Rinv_opp; RIneq.Rinv_r;
       Rdefinitions.Rle; RIneq.Rle_0_1; RIneq.Rle_0_sqr; RIneq.Rle_Reflexive;
       RIneq.Rle_Transitive; Rbasic_fun.Rle_abs; RIneq.Rle_antisym;
       OrderedRing.Rle_antisymm; RIneq.Rle_dec; RIneq.Rle_ge;
       OrderedRing.Rle_gt_cases; RIneq.Rle_le_eq; OrderedRing.Rle_le_minus;
       RIneq.Rle_lt_dec; OrderedRing.Rle_lt_eq; OrderedRing.Rle_lt_trans;
       RIneq.Rle_lt_trans; OrderedRing.Rle_ngt; RIneq.Rle_not_lt;
       OrderedRing.Rle_refl; RIneq.Rle_refl; OrderedRing.Rle_trans;
       RIneq.Rle_trans; Rdefinitions.RbaseSymbolsImpl.Rlt; RIneq.Rlt_0_1;
       RIneq.Rlt_0_2; RIneq.Rlt_0_minus; RIneq.Rlt_0_sqr; Raxioms.Rlt_asym;
       RIneq.Rlt_dec; Rdefinitions.RbaseSymbolsImpl.Rlt_def;
       RIneq.Rlt_dichotomy_converse; RIneq.Rlt_gt; RIneq.Rlt_irrefl;
       RIneq.Rlt_le; RIneq.Rlt_le_dec; OrderedRing.Rlt_le_neq;
       OrderedRing.Rlt_le_trans; RIneq.Rlt_le_trans; OrderedRing.Rlt_lt_minus;
       OrderedRing.Rlt_neq; OrderedRing.Rlt_nge; RIneq.Rlt_not_eq;
       RIneq.Rlt_not_ge; RIneq.Rlt_not_le; RIneq.Rlt_or_le;
       OrderedRing.Rlt_trans; Raxioms.Rlt_trans; OrderedRing.Rlt_trichotomy;
       BinNat.N.Rlt_wd; PeanoNat.Nat.Rlt_wd; BinInt.Z.Rlt_wd; Rbasic_fun.Rmax;
       Rbasic_fun.Rmax_Rlt; Rbasic_fun.Rmax_case_strong; Rbasic_fun.Rmax_l;
       Rbasic_fun.Rmax_left; Rbasic_fun.Rmax_lub_lt; Rbasic_fun.Rmax_r;
       Rbasic_fun.Rmax_right; Rbasic_fun.Rmax_stable_in_negreal;
       Rbasic_fun.Rmin; Rbasic_fun.Rmin_Rgt; Rbasic_fun.Rmin_Rgt_l;
       Rbasic_fun.Rmin_Rgt_r; Rbasic_fun.Rmin_case_strong;
       Rbasic_fun.Rmin_glb_lt; Rbasic_fun.Rmin_l; Rbasic_fun.Rmin_r;
       Rbasic_fun.Rmin_stable_in_posreal; Rdefinitions.Rminus;
       RIneq.Rminus_0_r; RIneq.Rminus_diag_eq; RIneq.Rminus_diag_uniq;
       RIneq.Rminus_diag_uniq_sym; OrderedRing.Rminus_eq_0;
       RIneq.Rminus_eq_contra; RIneq.Rminus_ge; RIneq.Rminus_gt;
       RIneq.Rminus_le; RIneq.Rminus_lt; RIneq.Rminus_not_eq;
       RIneq.Rminus_plus_distr; RIneq.Rminus_plus_l_l; RIneq.Rminus_plus_r_l;
       RIneq.Rminus_plus_r_r; Ring_theory.Rmul_0_l; Ring_theory.Rmul_1_l;
       Ring_theory.Rmul_assoc; Ring_theory.Rmul_comm; Ring_theory.Rmul_ext;
       Rdefinitions.RbaseSymbolsImpl.Rmult; RIneq.Rmult_0_l; RIneq.Rmult_0_r;
       Raxioms.Rmult_1_l; RIneq.Rmult_1_r; Raxioms.Rmult_assoc;
       Raxioms.Rmult_comm; Rdefinitions.RbaseSymbolsImpl.Rmult_def;
       RIneq.Rmult_div_l; RIneq.Rmult_div_r; RIneq.Rmult_eq_compat_l;
       RIneq.Rmult_eq_reg_l; RIneq.Rmult_ge_0_gt_0_lt_compat;
       RIneq.Rmult_gt_0_compat; RIneq.Rmult_integral;
       RIneq.Rmult_integral_contrapositive;
       RIneq.Rmult_integral_contrapositive_currified; RIneq.Rmult_inv_r_id_l;
       RIneq.Rmult_inv_r_id_m; RIneq.Rmult_inv_r_uniq;
       RIneq.Rmult_le_0_lt_compat; RIneq.Rmult_le_compat;
       RIneq.Rmult_le_compat_l; RIneq.Rmult_le_compat_neg_l;
       RIneq.Rmult_le_compat_r; RIneq.Rmult_le_pos; RIneq.Rmult_lt_0_compat;
       Raxioms.Rmult_lt_compat_l; RIneq.Rmult_lt_compat_r;
       RIneq.Rmult_lt_gt_compat_neg_l; RIneq.Rmult_lt_reg_l; RIneq.Rmult_ne;
       RIneq.Rmult_opp_opp; Raxioms.Rmult_plus_distr_l;
       RIneq.Rmult_plus_distr_r; RMicromega.Rnegate; OrderedRing.Rneq_symm;
       RMicromega.Rnormalise; RIneq.Rnot_gt_ge; RIneq.Rnot_le_gt;
       RIneq.Rnot_le_lt; RIneq.Rnot_lt_ge; RIneq.Rnot_lt_le;
       Rdefinitions.RbaseSymbolsImpl.Ropp; RIneq.Ropp_0; Rbasic_fun.Ropp_Rmin;
       RIneq.Ropp_Ropp_IZR; Ring_theory.Ropp_add; Ring_theory.Ropp_def;
       Rdefinitions.RbaseSymbolsImpl.Ropp_def; RIneq.Ropp_eq_0_compat;
       RIneq.Ropp_eq_compat; RIneq.Ropp_eq_reg; Ring_theory.Ropp_ext;
       RIneq.Ropp_ge_cancel; RIneq.Ropp_ge_le_contravar;
       RIneq.Ropp_gt_lt_0_contravar; RIneq.Ropp_gt_lt_contravar;
       RIneq.Ropp_involutive; RIneq.Ropp_le_cancel; RIneq.Ropp_le_contravar;
       RIneq.Ropp_le_ge_contravar; RIneq.Ropp_lt_cancel;
       RIneq.Ropp_lt_contravar; RIneq.Ropp_lt_gt_0_contravar;
       RIneq.Ropp_lt_gt_contravar; OrderedRing.Ropp_lt_mono;
       RIneq.Ropp_minus_distr; Ring_theory.Ropp_mul_l; RIneq.Ropp_mult_distr_l;
       RIneq.Ropp_mult_distr_l_reverse; RIneq.Ropp_mult_distr_r;
       RIneq.Ropp_neq_0_compat; Ring_theory.Ropp_opp; RIneq.Ropp_plus_distr;
       OrderedRing.Ropp_pos_neg; RingMicromega.Rops_wd;
       Rdefinitions.RbaseSymbolsImpl.Rplus; OrderedRing.Rplus_0_l;
       Raxioms.Rplus_0_l; OrderedRing.Rplus_0_r; RIneq.Rplus_0_r;
       RIneq.Rplus_0_r_uniq; Raxioms.Rplus_assoc; OrderedRing.Rplus_cancel_l;
       OrderedRing.Rplus_comm; Raxioms.Rplus_comm;
       Rdefinitions.RbaseSymbolsImpl.Rplus_def; RIneq.Rplus_diag;
       RIneq.Rplus_eq_compat_l; RIneq.Rplus_eq_compat_r; RIneq.Rplus_eq_reg_l;
       RIneq.Rplus_ge_compat_l; RIneq.Rplus_ge_compat_r; RIneq.Rplus_ge_reg_r;
       RIneq.Rplus_half_diag; RIneq.Rplus_le_compat; RIneq.Rplus_le_compat_l;
       RIneq.Rplus_le_compat_r; RIneq.Rplus_le_lt_0_compat;
       RIneq.Rplus_le_lt_0_neq_0; RIneq.Rplus_le_lt_compat;
       OrderedRing.Rplus_le_lt_mono; OrderedRing.Rplus_le_mono;
       OrderedRing.Rplus_le_mono_l; OrderedRing.Rplus_le_mono_r;
       RIneq.Rplus_le_reg_l; RIneq.Rplus_le_reg_r; RIneq.Rplus_lt_0_compat;
       RIneq.Rplus_lt_compat; Raxioms.Rplus_lt_compat_l;
       RIneq.Rplus_lt_compat_r; RIneq.Rplus_lt_le_0_compat;
       RIneq.Rplus_lt_le_compat; OrderedRing.Rplus_lt_le_mono;
       OrderedRing.Rplus_lt_mono; OrderedRing.Rplus_lt_mono_l;
       OrderedRing.Rplus_lt_mono_r; RIneq.Rplus_lt_reg_l; RIneq.Rplus_lt_reg_r;
       RIneq.Rplus_minus_assoc; RIneq.Rplus_minus_l; RIneq.Rplus_minus_r;
       RIneq.Rplus_ne; OrderedRing.Rplus_nonneg_nonneg;
       OrderedRing.Rplus_nonneg_pos; RIneq.Rplus_opp_l; Raxioms.Rplus_opp_r;
       RIneq.Rplus_opp_r_uniq; OrderedRing.Rplus_pos_nonneg;
       OrderedRing.Rplus_pos_pos; Rdefinitions.RbaseSymbolsImpl.Rquot1;
       Rdefinitions.RbaseSymbolsImpl.Rquot2;
       Rdefinitions.RbaseSymbolsImpl.Rrepr; Raxioms.Rrepr_0; Raxioms.Rrepr_1;
       Rdefinitions.Rrepr_appart_0; Raxioms.Rrepr_le; Raxioms.Rrepr_mult;
       Raxioms.Rrepr_opp; Raxioms.Rrepr_plus; Field_theory.Rring_ring_lemma1;
       RMicromega.Rsor; RIneq.Rsqr; RIneq.Rsqr_0_uniq; RIneq.Rsqr_def;
       RMicromega.Rsrt; Ring_theory.Rsub_def; Ring_theory.Rth_ARth;
       OrderedRing.Rtimes_0_l; OrderedRing.Rtimes_0_r; OrderedRing.Rtimes_comm;
       OrderedRing.Rtimes_neg_neg; OrderedRing.Rtimes_neq_0;
       OrderedRing.Rtimes_nonneg_nonneg; OrderedRing.Rtimes_pos_neg;
       OrderedRing.Rtimes_pos_pos; OrderedRing.Rtimes_square_nonneg;
       RIneq.Rtotal_order; ConstructiveRcomplete.Rup_pos;
       RingMicromega.SORRing_ring_lemma1; OrderedRing.SOR_ring_lemma1;
       RingMicromega.SORcleb_morph; RingMicromega.SORcneqb_morph;
       OrderedRing.SORle_antisymm; OrderedRing.SORle_refl;
       OrderedRing.SORle_trans; OrderedRing.SORle_wd; OrderedRing.SORlt_le_neq;
       OrderedRing.SORlt_trichotomy; OrderedRing.SORlt_wd;
       OrderedRing.SORopp_wd; OrderedRing.SORplus_le_mono_l;
       OrderedRing.SORplus_wd; RingMicromega.SORpower; RingMicromega.SORrm;
       OrderedRing.SORrt; OrderedRing.SORsetoid; OrderedRing.SORtimes_pos_pos;
       OrderedRing.SORtimes_wd; Ring_theory.SRadd_0_l; Ring_theory.SRadd_assoc;
       Ring_theory.SRadd_comm; Ring_theory.SRadd_ext; Ring_theory.SRdistr_l;
       Ring_theory.SReqe_Reqe; Ring_theory.SRmul_0_l; Ring_theory.SRmul_1_l;
       Ring_theory.SRmul_assoc; Ring_theory.SRmul_comm; Ring_theory.SRmul_ext;
       Ring_theory.SRopp; Ring_theory.SRopp_add; Ring_theory.SRopp_ext;
       Ring_theory.SRopp_mul_l; Ring_theory.SRsub; Ring_theory.SRsub_def;
       Ring_theory.SRth_ARth; Setoid.Seq_refl; Setoid.Seq_sym;
       Setoid.Seq_trans; Setoid.Setoid_Theory; Ring_theory.Smorph0;
       Ring_theory.Smorph1; Ring_theory.Smorph_add; Ring_theory.Smorph_eq;
       Ring_theory.Smorph_morph; Ring_theory.Smorph_mul;
       Ring_theory.Smorph_opp; Ring_theory.Smorph_sub;
       RelationClasses.StrictOrder_Irreflexive;
       RelationClasses.StrictOrder_Transitive; CRelationClasses.Symmetric;
       RelationClasses.Symmetric; Tauto.TFormula; CRelationClasses.Transitive;
       RelationClasses.Transitive; ConstructiveRcomplete.Un_cauchy_mod;
       Rseries.Un_cv; ConstructiveLimits.Un_cv_nat_real; Init.Unconvertible;
       ConstructiveCauchyRealsMult.Weaken_Qle_QpowerAddExp;
       ConstructiveCauchyRealsMult.Weaken_Qle_QpowerFac;
       ConstructiveCauchyRealsMult.Weaken_Qle_QpowerRemSubExp;
       ZMicromega.ZChecker; ZMicromega.ZChecker_sound; ZMicromega.ZNpower;
       ZMicromega.ZSORaddon; ZMicromega.ZTautoChecker;
       ZMicromega.ZTautoChecker_sound; ZMicromega.ZWitness; Znat.Z_N_nat;
       RIneq.Z_R_minus; ZArith_dec.Z_dec'; Zdiv.Z_div_mod;
       Zdiv.Z_div_mod_eq_full; ConstructiveExtra.Z_inj_nat;
       ConstructiveExtra.Z_inj_nat_id; ConstructiveExtra.Z_inj_nat_rev;
       ZArith_dec.Z_le_lt_eq_dec; ZArith_dec.Z_lt_dec; ZArith_dec.Z_lt_ge_dec;
       ZArith_dec.Z_lt_le_dec; Znumtheory.Z_lt_neq; Zdiv.Z_mod_lt;
       Zdiv.Z_mod_mult; Field_theory.Z_pos_sub_gt; BinNums.Z_rec;
       BinNums.Z_rect; Zcompare.Zcompare_mult_compat; ZArith_dec.Zcompare_rec;
       ZArith_dec.Zcompare_rect; ZMicromega.Zdeduce; ZMicromega.Zdiv_pol;
       ZMicromega.Zdiv_pol_correct; Znumtheory.Zdivide_Zdiv_eq;
       ZMicromega.Zdivide_ceiling; Znumtheory.Zdivide_mod;
       Znumtheory.Zdivide_opp_r; ZMicromega.Zdivide_pol_Zdivide;
       ZMicromega.Zdivide_pol_ind; ZMicromega.Zdivide_pol_one;
       ZMicromega.Zdivide_pol_sub; Zbool.Zeq_bool; RIneq.Zeq_bool_IZR;
       Zbool.Zeq_bool_eq; Zbool.Zeq_bool_neq; Zbool.Zeq_is_eq_bool;
       ZMicromega.Zeval_bop2; ZMicromega.Zeval_expr;
       ZMicromega.Zeval_expr_compat; ZMicromega.Zeval_formula;
       ZMicromega.Zeval_formula'; ZMicromega.Zeval_formula_compat;
  ...TRUNCATED BY DUNE...
       BinPos.Pos.add_reg_r; BinInt.Z.add_simpl_r; BinNat.N.add_sub;
       BinPos.Pos.add_sub; BinNat.N.add_sub_assoc; BinPos.Pos.add_sub_assoc;
       BinInt.Z.add_sub_assoc; BinNat.N.add_succ_l; PeanoNat.Nat.add_succ_l;
       BinPos.Pos.add_succ_l; BinInt.Z.add_succ_l; BinNat.N.add_succ_r;
       PeanoNat.Nat.add_succ_r; BinPos.Pos.add_succ_r; BinInt.Z.add_succ_r;
       Tauto.add_term; Tauto.add_term_correct; BinNat.N.add_wd;
       PeanoNat.Nat.add_wd; BinInt.Z.add_wd; PeanoNat.Nat.add_wd_obligation_1;
       BinPos.Pos.add_xI_pred_double; BinPos.Pos.add_xO; Rlimit.adhDa;
       Rtopology.adherence; Rtopology.adherence_P1; Rtopology.adherence_P2;
       Rtopology.adherence_P3; ZMicromega.agree_env;
       ZMicromega.agree_env_eval_nformula; ZMicromega.agree_env_eval_nformulae;
       ZMicromega.agree_env_jump; ZMicromega.agree_env_subset;
       ZMicromega.agree_env_tail; all; Morphisms_Prop.all_iff_morphism;
       Morphisms_Prop.all_iff_morphism_obligation_1; and_assoc; Tauto.and_cnf;
       Tauto.and_cnf_opt; Tauto.and_cnf_opt_cnf_ff_r; Tauto.and_cnf_opt_cnf_tt;
       and_comm; and_iff_compat_l; Morphisms_Prop.and_iff_morphism;
       Morphisms_Prop.and_iff_morphism_obligation_1; and_ind;
       ZifyClasses.and_morph; and_rec; and_rect; andb; Bool.andb_false_iff;
       andb_prop; Bool.andb_true_iff; app; CRelationClasses.arrow;
       CRelationClasses.arrow_Transitive;
       CRelationClasses.arrow_Transitive_obligation_1; ZMicromega.bdepth;
       BinNat.N.bi_induction; PeanoNat.Nat.bi_induction; BinInt.Z.bi_induction;
       ConstructiveCauchyReals.bound; Raxioms.bound; ZMicromega.bound_var;
       Rtopology.bounded; BinNat.N.case_analysis; PeanoNat.Nat.case_analysis;
       ConstructiveCauchyReals.cauchy; ZMicromega.ceiling;
       BinNat.N.central_induction; PeanoNat.Nat.central_induction;
       BinInt.Z.central_induction; EnvRing.ceqb_spec; Field_theory.ceqb_spec;
       Ring_polynom.ceqb_spec; Field_theory.ceqb_spec';
       RingMicromega.check_inconsistent;
       RingMicromega.check_inconsistent_sound;
       RingMicromega.check_normalised_formulas; RingMicromega.checker_nf_sound;
       Classical_Prop.classic; Tauto.clause; RingMicromega.cleb_sound;
       Rtopology.closed_set; Rtopology.closed_set_P1; RingMicromega.cltb;
       RingMicromega.cltb_sound; RingMicromega.cneqb;
       RingMicromega.cneqb_sound; Tauto.cnf; Tauto.cnf_checker;
       Tauto.cnf_checker_sound; Tauto.cnf_ff; RingMicromega.cnf_negate;
       RingMicromega.cnf_negate_correct; RingMicromega.cnf_normalise;
       RingMicromega.cnf_normalise_correct; RingMicromega.cnf_of_list;
       ZMicromega.cnf_of_list; RingMicromega.cnf_of_list_correct;
       ZMicromega.cnf_of_list_correct; Tauto.cnf_tt; Rtopology.compact;
       Rtopology.compact_EMP; Rtopology.compact_P1; Rtopology.compact_P2;
       Rtopology.compact_P3; Rtopology.compact_eqDom; PeanoNat.Nat.compare;
       BinNat.N.compare; BinPos.Pos.compare; BinInt.Z.compare;
       BinNat.N.compare_antisym; PeanoNat.Nat.compare_antisym;
       BinPos.Pos.compare_antisym; BinInt.Z.compare_antisym;
       BinPos.Pos.compare_cont; BinPos.Pos.compare_cont_antisym;
       BinPos.Pos.compare_cont_spec; BinNat.N.compare_eq_iff;
       PeanoNat.Nat.compare_eq_iff; BinPos.Pos.compare_eq_iff;
       BinInt.Z.compare_eq_iff; PeanoNat.Nat.compare_ge_iff;
       PeanoNat.Nat.compare_gt_iff; BinInt.Z.compare_gt_iff;
       BinNat.N.compare_le_iff; PeanoNat.Nat.compare_le_iff;
       BinPos.Pos.compare_le_iff; BinInt.Z.compare_le_iff;
       BinNat.N.compare_lt_iff; PeanoNat.Nat.compare_lt_iff;
       BinPos.Pos.compare_lt_iff; BinInt.Z.compare_lt_iff;
       BinNat.N.compare_nge_iff; BinInt.Z.compare_nge_iff;
       BinInt.Z.compare_ngt_iff; BinNat.N.compare_nle_iff;
       BinInt.Z.compare_nle_iff; BinNat.N.compare_refl;
       PeanoNat.Nat.compare_refl; BinPos.Pos.compare_refl;
       BinInt.Z.compare_refl; BinNat.N.compare_spec; PeanoNat.Nat.compare_spec;
       BinPos.Pos.compare_spec; Qminmax.Q.OT.compare_spec;
       BinInt.Z.compare_spec; BinInt.Z.compare_sub;
       BinPos.Pos.compare_sub_mask; PeanoNat.Nat.compare_succ;
       BinPos.Pos.compare_succ_l; BinPos.Pos.compare_succ_r;
       BinPos.Pos.compare_succ_succ; BinPos.Pos.compare_xI_xI;
       BinPos.Pos.compare_xI_xO; BinPos.Pos.compare_xO_xI;
       BinPos.Pos.compare_xO_xO; RelationClasses.complement;
       Rtopology.complementary; Raxioms.completeness; Rtopology.cond_fam;
       RIneq.cond_neg; RIneq.cond_pos; Field_theory.condition;
       ConstructiveEpsilon.constructive_indefinite_ground_description;
       ConstructiveExtra.constructive_indefinite_ground_description_Z;
       ConstructiveEpsilon.constructive_indefinite_ground_description_nat;
       Rderiv.cont_deriv; Rderiv.continue_in; Ranalysis1.continuity;
       Rtopology.continuity_P1; Rtopology.continuity_P2;
       Rtopology.continuity_ab_maj; Rtopology.continuity_ab_min;
       Rtopology.continuity_compact; Ranalysis1.continuity_pt;
       Ranalysis1.continuity_pt_minus; Ranalysis1.continuity_pt_mult;
       Ranalysis1.continuity_pt_opp; Rtopology.covering;
       Rtopology.covering_finite; Rtopology.covering_open_set;
       CRelationClasses.crelation; Field_theory.cross_product_eq;
       ZMicromega.cutting_plane_sound; Decidable.decidable;
       Field_theory.default_isIn; Field_theory.default_isIn_ok;
       SetoidTactics.default_relation; Field_theory.denum;
       Ranalysis1.deriv_constant2; Ranalysis1.deriv_maximum;
       Ranalysis1.deriv_minimum; Ranalysis1.derivable;
       Ranalysis1.derivable_const; Ranalysis1.derivable_continuous;
       Ranalysis1.derivable_continuous_pt; Ranalysis1.derivable_derive;
       Ranalysis1.derivable_id; Ranalysis1.derivable_pt;
       Ranalysis1.derivable_pt_abs; Ranalysis1.derivable_pt_const;
       Ranalysis1.derivable_pt_id; Ranalysis1.derivable_pt_lim;
       Ranalysis1.derivable_pt_lim_D_in; Ranalysis1.derivable_pt_lim_const;
       Ranalysis1.derivable_pt_lim_id; Ranalysis1.derivable_pt_lim_minus;
       Ranalysis1.derivable_pt_lim_mult; Ranalysis1.derivable_pt_lim_opp;
       Ranalysis1.derivable_pt_lim_opp_fwd; Ranalysis1.derivable_pt_minus;
       Ranalysis1.derivable_pt_mult; Ranalysis1.derivable_pt_opp;
       Ranalysis1.derive_pt; Ranalysis1.derive_pt_D_in;
       Ranalysis1.derive_pt_const; Ranalysis1.derive_pt_eq;
       Ranalysis1.derive_pt_eq_0; Ranalysis1.derive_pt_eq_1;
       Ranalysis1.derive_pt_id; Ranalysis1.derive_pt_minus;
       Ranalysis1.derive_pt_mult; Ranalysis1.derive_pt_opp;
       Bool.diff_false_true; Rtopology.disc; Rtopology.disc_P1;
       Field_theory.display_pow_linear; Rlimit.dist; BinInt.Z.div;
       BinNat.N.div_eucl; BinInt.Z.div_eucl; BinInt.Z.div_eucl_eq;
       BinNat.N.div_eucl_spec; Ring_theory.div_eucl_th; BinInt.Z.div_mod;
       BinInt.Z.Private_NZDiv.div_mod_unique; BinInt.Z.div_mod_unique;
       BinInt.Z.div_mul; BinInt.Z.div_unique; BinInt.Z.div_unique_exact;
       BinInt.Z.div_wd; BinPos.Pos.divide; BinInt.Z.divide;
       BinInt.Z.divide_Zpos; BinInt.Z.divide_Zpos_Zneg_l;
       BinInt.Z.divide_Zpos_Zneg_r; BinInt.Z.divide_abs_l;
       BinInt.Z.divide_abs_r; BinPos.Pos.divide_add_cancel_l;
       BinInt.Z.divide_antisym; BinInt.Z.divide_antisym_abs;
       BinInt.Z.divide_antisym_nonneg; BinPos.Pos.divide_mul_l;
       BinPos.Pos.divide_mul_r; BinInt.Z.divide_opp_l; BinInt.Z.divide_opp_r;
       BinInt.Z.divide_refl; BinInt.Z.divide_trans; BinInt.Z.divide_wd;
       BinPos.Pos.divide_xO_xI; BinPos.Pos.divide_xO_xO;
       Rtopology.domain_finite; BinNat.N.double; BinInt.Z.double;
       BinNat.N.double_add; BinPos.Pos.double_mask; BinNat.N.double_mul;
       BinPos.Pos.double_pred_mask; Tauto.eAND; Tauto.eAnd_morph_Proper;
       Tauto.eFF; Tauto.eIFF; Tauto.eIFF_morph_Proper; Tauto.eIMPL;
       Tauto.eIMPL_morph_Proper; Tauto.eKind; Tauto.eNOT;
       Tauto.eNOT_morph_Proper; Tauto.eOR; Tauto.eOR_morph_Proper; Tauto.eTT;
       Tauto.e_rtyp; Tauto.eiff; Tauto.eiff_eq; Tauto.eiff_refl;
       Tauto.eiff_sym; Tauto.eiff_trans; Ztac.elim_concl_le; EnvRing.env_morph;
       Rlimit.eps2; Rlimit.eps2_Rgt_R0; BinNat.N.eq; BinInt.Z.eq;
       RingMicromega.eq0_cnf; Qreals.eqR_Qeq; Rtopology.eq_Dom; RIneq.eq_IZR;
       RIneq.eq_IZR_R0; RIneq.eq_IZR_contrapositive;
       RelationClasses.eq_Reflexive; RelationClasses.eq_Symmetric;
       RelationClasses.eq_Transitive; eq_add_S; ZMicromega.eq_cnf;
       BinPos.Pos.eq_dec; BinInt.Z.eq_dec; BinInt.Z.eq_decidable;
       BinNat.N.Private_OrderTac.IsTotal.eq_equiv;
       PeanoNat.Nat.Private_OrderTac.IsTotal.eq_equiv;
       BinInt.Z.Private_OrderTac.IsTotal.eq_equiv; BinNat.N.eq_equiv;
       PeanoNat.Nat.eq_equiv; BinPos.Pos.eq_equiv; Qminmax.Q.OT.eq_equiv;
       BinInt.Z.eq_equiv; RelationClasses.eq_equivalence; Ztac.eq_incl; eq_ind;
       eq_ind_r; BinPos.Pos.Private_Tac.eq_le; Qminmax.Q.Private_Tac.eq_le;
       BinInt.Z.Private_Tac.eq_le; BinInt.Z.Private_OrderTac.Tac.eq_le;
       ZMicromega.eq_le_iff; BinNat.N.eq_le_incl; PeanoNat.Nat.eq_le_incl;
       BinInt.Z.eq_le_incl; PeanoNat.Nat.Private_Tac.eq_lt;
       BinPos.Pos.Private_Tac.eq_lt; Qminmax.Q.Private_Tac.eq_lt;
       BinInt.Z.Private_Tac.eq_lt; BinInt.Z.Private_OrderTac.Tac.eq_lt;
       BinInt.Z.eq_mul_0; BinInt.Z.eq_mul_1_nonneg; BinInt.Z.eq_mul_1_nonneg';
       BinPos.Pos.Private_Tac.eq_neq; BinInt.Z.Private_OrderTac.Tac.eq_neq;
       BinInt.Z.eq_opp_l; ZifyInst.eq_pos_inj; Morphisms.eq_proper_proxy;
       eq_rec; eq_rec_r; eq_rect; BinPos.Pos.Private_Tac.eq_refl;
       BinInt.Z.Private_OrderTac.Tac.eq_refl; BinInt.Z.eq_refl; eq_sym;
       PeanoNat.Nat.Private_Tac.eq_sym; BinPos.Pos.Private_Tac.eq_sym;
       Qminmax.Q.Private_Tac.eq_sym; BinInt.Z.Private_Tac.eq_sym;
       BinInt.Z.Private_OrderTac.Tac.eq_sym; BinInt.Z.eq_sym_iff; eq_trans;
       BinPos.Pos.Private_Tac.eq_trans; BinInt.Z.Private_OrderTac.Tac.eq_trans;
       Bool.eqb; BinNat.N.eqb; BinPos.Pos.eqb; BinInt.Z.eqb; BinNat.N.eqb_eq;
       BinPos.Pos.eqb_eq; BinInt.Z.eqb_eq; BinPos.Pos.eqb_neq;
       BinPos.Pos.eqb_refl; BinNat.N.eqb_spec; BinPos.Pos.eqb_spec;
       Bool.eqb_true_iff; SetoidTactics.equivalence_default;
       RelationClasses.equivalence_rewrite_relation; RingMicromega.eval_Psatz;
       ZMicromega.eval_Psatz; RingMicromega.eval_Psatz_Sound;
       ZMicromega.eval_Psatz_sound; Tauto.eval_bf; Tauto.eval_bf_map;
       Tauto.eval_clause; Tauto.eval_cnf; Tauto.eval_cnf_and_opt;
       Tauto.eval_cnf_app; Tauto.eval_cnf_cons_iff; Tauto.eval_cnf_ff;
       Tauto.eval_cnf_tt; ZMicromega.eval_expr; Tauto.eval_f;
       Tauto.eval_f_morph; RingMicromega.eval_formula;
       RingMicromega.eval_formulaSC; RingMicromega.eval_nformula;
       ZMicromega.eval_nformula; ZMicromega.eval_nformula_bound_var;
       RingMicromega.eval_nformula_dec; ZMicromega.eval_nformula_mk_eq_pos;
       ZMicromega.eval_nformula_split; RingMicromega.eval_op1;
       RingMicromega.eval_op2; Tauto.eval_opt_clause; RingMicromega.eval_pexpr;
       RingMicromega.eval_pexprSC; RingMicromega.eval_pol; ZMicromega.eval_pol;
       ZMicromega.eval_pol_Pc; RingMicromega.eval_pol_add;
       ZMicromega.eval_pol_add; RingMicromega.eval_pol_norm;
       ZMicromega.eval_pol_norm; RingMicromega.eval_pol_opp;
       RingMicromega.eval_pol_sub; ZMicromega.eval_pol_sub;
       RingMicromega.eval_sexpr; RingMicromega.eval_sformula; Tauto.eval_tt;
       Morphisms_Prop.ex_iff_morphism;
       Morphisms_Prop.ex_iff_morphism_obligation_1; ex_ind; Rtopology.f;
       f_equal; f_equal_nat; Rtopology.family_finite;
       Rtopology.family_open_set; Field_theory.fcons_ok; Ranalysis1.fct_cte;
       Field_theory.field_is_integral_domain; VarMap.find; Basics.flip;
       CRelationClasses.flip; CMorphisms.flip1; CMorphisms.flip2;
       RelationClasses.flip_Reflexive; List.fold_left; List.fold_right; fst;
       BinPos.Pos.gcd; BinInt.Z.gcd; BinInt.Z.gcd_divide_l;
       BinInt.Z.gcd_divide_r; BinPos.Pos.gcd_greatest; BinInt.Z.gcd_greatest;
       BinInt.Z.gcd_nonneg; BinPos.Pos.gcdn; BinPos.Pos.gcdn_greatest; ge;
       BinPos.Pos.ge; BinInt.Z.ge; BinInt.Z.ge_le; BinPos.Pos.ge_le_iff;
       BinInt.Z.ge_le_iff; BinInt.Z.geb; BinInt.Z.geb_le; BinInt.Z.geb_leb;
       ZMicromega.genCuttingPlane; ZMicromega.genCuttingPlaneNone;
       InitialRing.gen_Zeqb_ok; InitialRing.gen_phiN; InitialRing.gen_phiN1;
       InitialRing.gen_phiN_add; InitialRing.gen_phiN_morph;
       InitialRing.gen_phiN_mult; InitialRing.gen_phiN_sub;
       InitialRing.gen_phiPOS; InitialRing.gen_phiPOS1; InitialRing.gen_phiZ;
       InitialRing.gen_phiZ1; InitialRing.gen_phiZ1_pos_sub;
       InitialRing.gen_phiZ_add; InitialRing.gen_phiZ_ext;
       InitialRing.gen_phiZ_morph; InitialRing.gen_phiZ_mul; EnvRing.get_PEopp;
       Ring_polynom.get_PEopp; InitialRing.get_signZ; InitialRing.get_signZ_th;
       Ring_theory.get_sign_None; Ring_theory.get_sign_None_th;
       BinPos.Pos.ggcd; BinInt.Z.ggcd; BinPos.Pos.ggcd_correct_divisors;
       BinInt.Z.ggcd_correct_divisors; BinPos.Pos.ggcd_gcd; BinInt.Z.ggcd_gcd;
       BinPos.Pos.ggcdn; BinPos.Pos.ggcdn_correct_divisors;
       BinPos.Pos.ggcdn_gcdn; ConstructiveLUB.glb_dec_Q; BinPos.Pos.gt;
       BinInt.Z.gt; BinPos.Pos.gt_lt; BinInt.Z.gt_lt; BinPos.Pos.gt_lt_iff;
       BinInt.Z.gt_lt_iff; BinInt.Z.gt_wf; BinInt.Z.gtb; BinInt.Z.gtb_ltb;
       BinInt.Z.gtb_spec; Env.hd; List.hd; Tauto.hold; Tauto.hold_eAND;
       Tauto.hold_eEQ; Tauto.hold_eFF; Tauto.hold_eIFF; Tauto.hold_eIFF_IMPL;
       Tauto.hold_eIMPL; Tauto.hold_eNOT; Tauto.hold_eOR; Tauto.hold_eTT;
       Tauto.hold_eiff; id; Ranalysis1.id; Nnat.N2Nat.id; Znat.N2Z.id;
       Nnat.Nat2N.id; Pnat.Nat2Pos.id; Znat.Nat2Z.id; Pnat.Pos2Nat.id;
       Znat.Z2N.id; Znat.Z2Nat.id; BinInt.Z2Pos.id; Ring_theory.id_phi_N;
       Pnat.SuccNat2Pos.id_succ; Tauto.if_cnf_tt; Field_theory.if_true; iff;
       CRelationClasses.iffT; CMorphisms.iffT_arrow_subrelation;
       CMorphisms.iffT_flip_arrow_subrelation; RelationClasses.iff_Reflexive;
       RelationClasses.iff_Symmetric; RelationClasses.iff_Transitive;
       RelationClasses.iff_equivalence; Morphisms.iff_flip_impl_subrelation;
       Morphisms_Prop.iff_iff_iff_impl_morphism;
       Morphisms_Prop.iff_iff_iff_impl_morphism_obligation_1;
       Morphisms.iff_impl_subrelation; iff_refl; Bool.iff_reflect; iff_stepl;
       iff_sym; iff_trans; Rtopology.image_dir; Rtopology.image_rec;
       Basics.impl; RelationClasses.impl_Reflexive;
       RelationClasses.impl_Reflexive_obligation_1; implb;
       Classical_Prop.imply_to_and; ZMicromega.in_bdepth; Rtopology.included;
       Rtopology.included_trans; Rtopology.ind; BinNat.N.induction;
       PeanoNat.Nat.induction; ZifyClasses.inj; Nnat.N2Nat.inj; Znat.Nat2Z.inj;
       Pnat.Pos2Nat.inj; BinInt.Pos2Z.inj; Pnat.Pos2Nat.inj_1;
       Nnat.N2Nat.inj_add; Znat.N2Z.inj_add; Nnat.Nat2N.inj_add;
       Znat.Nat2Z.inj_add; Pnat.Pos2Nat.inj_add; BinInt.Pos2Z.inj_add;
       Nnat.N2Nat.inj_compare; Znat.N2Z.inj_compare; Nnat.Nat2N.inj_compare;
       Znat.Nat2Z.inj_compare; Pnat.Pos2Nat.inj_compare;
       Znat.Z2Nat.inj_compare; Znat.Nat2Z.inj_ge; Znat.Nat2Z.inj_iff;
       BinInt.Pos2Z.inj_iff; Znat.Nat2Z.inj_le; Pnat.Pos2Nat.inj_le;
       Znat.Z2Nat.inj_le; Znat.Nat2Z.inj_lt; Nnat.N2Nat.inj_max;
       Znat.N2Z.inj_max; Nnat.Nat2N.inj_max; Znat.Nat2Z.inj_max;
       Pnat.Pos2Nat.inj_mul; BinInt.Pos2Z.inj_mul; Znat.N2Z.inj_pos;
       BinInt.Pos2Z.inj_pow; BinInt.Pos2Z.inj_pow_pos; Znat.Nat2Z.inj_succ;
       Pnat.Pos2Nat.inj_succ; BinInt.Pos2Z.inj_succ; Pnat.Pos2Nat.inj_xI;
       Pnat.Pos2Nat.inj_xO; ConstructiveCauchyReals.inject_Q;
       ConstructiveCauchyReals.inject_Q_cauchy;
       ConstructiveCauchyReals.inject_Q_compare;
       ConstructiveCauchyReals.inject_Q_le;
       ConstructiveCauchyReals.inject_Q_lt;
       ConstructiveCauchyReals.inject_Q_morph;
       ConstructiveCauchyReals.inject_Q_morph_Proper;
       ConstructiveCauchyRealsMult.inject_Q_mult;
       ConstructiveCauchyReals.inject_Q_plus; ConstructiveCauchyReals.inject_Z;
       QArith_base.inject_Z; Rtopology.interior; Rtopology.interior_P1;
       Rtopology.interior_P2; Ring_polynom.interp_PElist;
       Ring_polynom.interp_PElist_ok; PeanoNat.Nat.Private_Tac.interp_ord;
       BinPos.Pos.Private_Tac.interp_ord; Qminmax.Q.Private_Tac.interp_ord;
       BinInt.Z.Private_Tac.interp_ord;
       BinNat.N.Private_OrderTac.Tac.interp_ord;
       PeanoNat.Nat.Private_OrderTac.Tac.interp_ord;
       BinInt.Z.Private_OrderTac.Tac.interp_ord; Rtopology.intersection_domain;
       Pnat.SuccNat2Pos.inv; ConstructiveEpsilon.inv_before_witness;
       Field_theory.isIn; Field_theory.isIn_ok;
       ConstructiveReals.isLinearOrder; Tauto.is_bool; Tauto.is_bool_inv;
       Tauto.is_cnf_ff; Tauto.is_cnf_ff_cnf_ff; Tauto.is_cnf_ff_inv;
       Tauto.is_cnf_tt; Tauto.is_cnf_tt_cnf_ff; Tauto.is_cnf_tt_inv;
       ConstructiveLUB.is_lub; Raxioms.is_lub; Znat.Nat2Z.is_nonneg;
       BinInt.Pos2Z.is_nonneg; ZMicromega.is_pol_Z0;
       ZMicromega.is_pol_Z0_eval_pol; Pnat.Pos2Nat.is_pos; BinInt.Pos2Z.is_pos;
       Pnat.Pos2Nat.is_succ; is_true; ConstructiveLUB.is_upper_bound;
       Raxioms.is_upper_bound; ConstructiveLUB.is_upper_bound_closed;
       ConstructiveLUB.is_upper_bound_dec;
       ConstructiveLUB.is_upper_bound_epsilon;
       ConstructiveLUB.is_upper_bound_glb;
       ConstructiveLUB.is_upper_bound_not_epsilon; BinPos.Pos.iter;
       BinPos.Pos.iter_add; BinPos.Pos.iter_ind; BinPos.Pos.iter_invariant;
       BinPos.Pos.iter_op; BinPos.Pos.iter_op_succ; BinPos.Pos.iter_succ;
       BinPos.Pos.iter_swap; BinPos.Pos.iter_swap_gen; BinList.jump; Env.jump;
       BinList.jump_add; Env.jump_add; Ring_polynom.jump_add';
       BinList.jump_pred_double; Env.jump_pred_double; Env.jump_simpl;
       BinList.jump_succ; BinList.jump_tl; BinNat.N.le; BinPos.Pos.le;
       BinInt.Z.le; ZMicromega.le_0_iff; BinNat.N.le_0_l; PeanoNat.Nat.le_0_l;
       le_0_n; BinInt.Z.le_0_sub; BinPos.Pos.le_1_l; le_S_n;
       BinInt.Z.le_add_le_sub_l; BinInt.Z.le_add_le_sub_r;
       BinPos.Pos.le_antisym; BinPos.Pos.Private_Tac.le_antisym;
       BinInt.Z.Private_OrderTac.Tac.le_antisym; BinInt.Z.le_antisymm;
       Qminmax.Q.Private_Tac.le_eq; BinInt.Z.Private_Tac.le_eq;
       BinInt.Z.Private_OrderTac.Tac.le_eq; BinInt.Z.le_exists_sub;
       BinInt.Z.le_ge; BinInt.Z.le_ge_cases; BinNat.N.le_gt_cases;
       PeanoNat.Nat.le_gt_cases; BinInt.Z.le_gt_cases; le_ind; BinInt.Z.le_ind;
       BinNat.N.le_le_succ_r; PeanoNat.Nat.le_le_succ_r; BinInt.Z.le_le_succ_r;
       BinInt.Z.le_lt_add_lt; Compare_dec.le_lt_dec;
       PeanoNat.Nat.Private_Tac.le_lt_trans;
       BinPos.Pos.Private_Tac.le_lt_trans; Qminmax.Q.Private_Tac.le_lt_trans;
       BinInt.Z.Private_Tac.le_lt_trans;
       BinNat.N.Private_OrderTac.Tac.le_lt_trans;
       PeanoNat.Nat.Private_OrderTac.Tac.le_lt_trans;
       BinInt.Z.Private_OrderTac.Tac.le_lt_trans; BinInt.Z.le_lt_trans;
       BinNat.N.Private_OrderTac.IsTotal.le_lteq;
       PeanoNat.Nat.Private_OrderTac.IsTotal.le_lteq;
       BinInt.Z.Private_OrderTac.IsTotal.le_lteq; BinNat.N.le_lteq;
       PeanoNat.Nat.le_lteq; BinPos.Pos.le_lteq; Qminmax.Q.OT.le_lteq;
       BinInt.Z.le_lteq; PeanoNat.Nat.le_max_l; BinPos.Pos.le_max_l;
       PeanoNat.Nat.le_max_r; BinPos.Pos.le_max_r; BinInt.Z.le_min_l; le_n_S;
       ZMicromega.le_neg; BinInt.Z.le_neq; BinPos.Pos.Private_Tac.le_neq_lt;
       BinInt.Z.Private_OrderTac.Tac.le_neq_lt; PeanoNat.Nat.le_ngt;
       BinInt.Z.le_ngt; BinPos.Pos.le_nlt; le_pred; BinNat.N.le_preorder;
       PeanoNat.Nat.le_preorder; BinInt.Z.le_preorder; BinNat.N.le_refl;
       PeanoNat.Nat.le_refl; BinPos.Pos.le_refl;
       BinInt.Z.Private_OrderTac.Tac.le_refl; BinInt.Z.le_refl;
       BinInt.Z.le_sub_le_add_l; BinInt.Z.le_sub_le_add_r; BinNat.N.le_succ_l;
       PeanoNat.Nat.le_succ_l; BinPos.Pos.le_succ_l; BinInt.Z.le_succ_l;
       BinNat.N.le_succ_r; PeanoNat.Nat.le_succ_r; BinInt.Z.le_succ_r;
       BinNat.N.le_trans; PeanoNat.Nat.le_trans; BinPos.Pos.le_trans;
       BinInt.Z.le_trans; BinNat.N.le_wd; PeanoNat.Nat.le_wd; BinInt.Z.le_wd;
       BinNat.N.leb; BinPos.Pos.leb; BinInt.Z.leb; BinInt.Z.leb_gt;
       BinNat.N.leb_le; BinPos.Pos.leb_le; BinInt.Z.leb_le; BinInt.Z.leb_nle;
       BinNat.N.leb_spec; BinInt.Z.leb_spec; BinNat.N.leb_spec0;
       BinInt.Z.leb_spec0; BinInt.Z.left_induction; Rlimit.limit1_in;
       Rlimit.limit_Ropp; Rlimit.limit_in; Rlimit.limit_minus;
       Rlimit.limit_mul; Rlimit.limit_plus;
       ConstructiveCauchyReals.linear_order_T;
       ConstructiveEpsilon.linear_search_conform;
       ConstructiveEpsilon.linear_search_from_0_conform; list_ind; list_rec;
       list_rect; Ring_polynom.local_mkpow_ok; lt; BinNat.N.lt; BinPos.Pos.lt;
       BinInt.Z.lt; BinInt.Z.lt_0_1; RIneq.lt_0_IZR; BinInt.Z.lt_0_sub;
       PeanoNat.Nat.lt_0_succ; BinInt.Z.lt_1_2; BinInt.Z.lt_1_l;
       BinInt.Z.lt_1_mul_pos; BinPos.Pos.lt_1_succ;
       ConstructiveReals.lt_CR_of_Q; RIneq.lt_IZR; BinInt.Z.lt_add_lt_sub_r;
       BinInt.Z.lt_add_pos_l; BinInt.Z.lt_add_pos_r; BinPos.Pos.lt_add_r;
       BinNat.N.lt_asymm; PeanoNat.Nat.lt_asymm; BinInt.Z.lt_asymm;
       BinNat.N.Private_OrderTac.IsTotal.lt_compat;
       PeanoNat.Nat.Private_OrderTac.IsTotal.lt_compat;
       BinInt.Z.Private_OrderTac.IsTotal.lt_compat; BinNat.N.lt_compat;
       PeanoNat.Nat.lt_compat; BinPos.Pos.lt_compat; Qminmax.Q.OT.lt_compat;
       BinInt.Z.lt_compat; BinPos.Pos.Private_Tac.lt_eq;
       Qminmax.Q.Private_Tac.lt_eq; BinInt.Z.Private_Tac.lt_eq;
       BinNat.N.Private_OrderTac.Tac.lt_eq;
       PeanoNat.Nat.Private_OrderTac.Tac.lt_eq;
       BinInt.Z.Private_OrderTac.Tac.lt_eq; BinNat.N.lt_eq_cases;
       PeanoNat.Nat.lt_eq_cases; BinPos.Pos.lt_eq_cases; BinInt.Z.lt_eq_cases;
       BinNat.N.lt_exists_pred; PeanoNat.Nat.lt_exists_pred;
       BinInt.Z.lt_exists_pred; BinInt.Z.lt_ge_cases; BinPos.Pos.lt_gt;
       BinInt.Z.lt_gt; BinInt.Z.lt_gt_cases; BinPos.Pos.lt_iff_add;
       BinNat.N.lt_ind; BinInt.Z.lt_ind; BinNat.N.lt_ind_rel;
       ConstructiveCauchyReals.lt_inject_Q; BinNat.N.lt_irrefl;
       PeanoNat.Nat.lt_irrefl; BinPos.Pos.lt_irrefl;
       PeanoNat.Nat.Private_Tac.lt_irrefl; BinPos.Pos.Private_Tac.lt_irrefl;
       Qminmax.Q.Private_Tac.lt_irrefl; BinInt.Z.Private_Tac.lt_irrefl;
       BinNat.N.Private_OrderTac.Tac.lt_irrefl;
       PeanoNat.Nat.Private_OrderTac.Tac.lt_irrefl;
       BinInt.Z.Private_OrderTac.Tac.lt_irrefl; BinInt.Z.lt_irrefl;
       ZMicromega.lt_le_iff; BinNat.N.lt_le_incl; PeanoNat.Nat.lt_le_incl;
       BinInt.Z.lt_le_incl; BinInt.Z.lt_le_pred; PeanoNat.Nat.lt_le_trans;
       BinPos.Pos.lt_le_trans; BinInt.Z.lt_le_trans; BinNat.N.lt_lt_succ_r;
       PeanoNat.Nat.lt_lt_succ_r; BinInt.Z.lt_lt_succ_r; BinInt.Z.lt_neq;
       BinInt.Z.lt_nge; BinPos.Pos.lt_nle;
       BinNat.N.Private_OrderTac.IsTotal.lt_strorder;
       PeanoNat.Nat.Private_OrderTac.IsTotal.lt_strorder;
       BinInt.Z.Private_OrderTac.IsTotal.lt_strorder; BinNat.N.lt_strorder;
       PeanoNat.Nat.lt_strorder; BinPos.Pos.lt_strorder;
       Qminmax.Q.OT.lt_strorder; BinInt.Z.lt_strorder;
       BinInt.Z.lt_sub_lt_add_r; BinNat.N.lt_succ_diag_r;
       PeanoNat.Nat.lt_succ_diag_r; BinPos.Pos.lt_succ_diag_r;
       BinInt.Z.lt_succ_diag_r; BinNat.N.lt_succ_l; BinInt.Z.lt_succ_l;
       BinNat.N.lt_succ_r; PeanoNat.Nat.lt_succ_r; BinPos.Pos.lt_succ_r;
       BinInt.Z.lt_succ_r; BinNat.N.Private_OrderTac.IsTotal.lt_total;
       PeanoNat.Nat.Private_OrderTac.IsTotal.lt_total;
       BinInt.Z.Private_OrderTac.IsTotal.lt_total; BinNat.N.lt_total;
       PeanoNat.Nat.lt_total; Qminmax.Q.OT.lt_total; BinPos.Pos.lt_total;
       BinInt.Z.lt_total; BinNat.N.lt_trans; PeanoNat.Nat.lt_trans;
       BinPos.Pos.lt_trans; PeanoNat.Nat.Private_Tac.lt_trans;
       BinPos.Pos.Private_Tac.lt_trans; BinInt.Z.Private_Tac.lt_trans;
       BinNat.N.Private_OrderTac.Tac.lt_trans;
       PeanoNat.Nat.Private_OrderTac.Tac.lt_trans;
       BinInt.Z.Private_OrderTac.Tac.lt_trans; BinInt.Z.lt_trans;
       BinNat.N.lt_trichotomy; PeanoNat.Nat.lt_trichotomy;
       BinInt.Z.lt_trichotomy; BinNat.N.lt_wd; PeanoNat.Nat.lt_wd;
       BinInt.Z.lt_wd; PeanoNat.Nat.lt_wd_obligation_1; BinNat.N.lt_wf;
       PeanoNat.Nat.lt_wf; BinInt.Z.lt_wf; BinInt.Z.ltb; BinInt.Z.ltb_ge;
       BinInt.Z.ltb_lt; BinInt.Z.ltb_nlt; BinInt.Z.ltb_spec;
       BinInt.Z.ltb_spec0; Wf_nat.ltof; ZMicromega.ltof_bdepth_split_l;
       ZMicromega.ltof_bdepth_split_r; ZMicromega.makeCuttingPlane;
       ZMicromega.makeCuttingPlane_ns_sound; Refl.make_conj;
       Refl.make_conj_app; Refl.make_conj_cons; Refl.make_conj_impl;
       Refl.make_conj_in; Refl.make_conj_rapp; Refl.make_impl;
       Refl.make_impl_map; List.map; RingMicromega.map_Formula;
       RingMicromega.map_PExpr; Tauto.map_bformula; RingMicromega.map_option;
       RingMicromega.map_option2; BinPos.Pos.mask2cmp; PeanoNat.Nat.max;
       BinNat.N.max; BinPos.Pos.max; BinInt.Z.max; BinPos.Pos.max_1_l;
       BinInt.Z.max_case; BinPos.Pos.max_case_strong;
       BinPos.Pos.Private_Dec.max_case_strong;
       BinInt.Z.Private_Dec.max_case_strong; BinInt.Z.max_case_strong;
       BinInt.Z.max_comm; max_l; PeanoNat.Nat.max_l; BinPos.Pos.max_l;
       BinInt.Z.max_l; BinPos.Pos.max_le_compat_r; BinPos.Pos.max_lub_iff;
       BinPos.Pos.max_mono; BinPos.Pos.max_monotone; max_r; PeanoNat.Nat.max_r;
       BinPos.Pos.max_r; BinInt.Z.max_r; PeanoNat.Nat.max_spec;
       BinPos.Pos.max_spec; BinInt.Z.max_spec; ZMicromega.max_var;
       ZMicromega.max_var_acc; ZMicromega.max_var_nformulae;
       ZMicromega.max_var_nformulae_mono_aux;
       ZMicromega.max_var_nformulae_mono_aux';
       RingMicromega.micomega_sor_setoid;
       RingMicromega.micomega_sor_setoid_Reflexive;
       RingMicromega.micomega_sor_setoid_Symmetric;
       RingMicromega.micomega_sor_setoid_Transitive; BinInt.Z.min;
       BinInt.Z.Private_Dec.min_case; BinInt.Z.Private_Dec.min_case_strong;
       BinInt.Z.Private_Dec.min_dec; BinInt.Z.min_dec; BinInt.Z.min_l;
       BinInt.Z.min_r; BinInt.Z.min_spec; RIneq.minus_IPR; RIneq.minus_IZR;
       Ranalysis1.minus_fct; EnvRing.mkPX; Ring_polynom.mkPX;
       Ring_polynom.mkPX_ext; EnvRing.mkPX_ok; Ring_polynom.mkPX_ok;
       EnvRing.mkPinj; Ring_polynom.mkPinj; Ring_polynom.mkPinj_ext;
       EnvRing.mkPinj_ok; Ring_polynom.mkPinj_ok; EnvRing.mkPinj_pred;
       Ring_polynom.mkPinj_pred; Ring_polynom.mkVmon; Ring_polynom.mkVmon_ok;
       EnvRing.mkX; Ring_polynom.mkX; EnvRing.mkX_ok; Ring_polynom.mkX_ok;
       EnvRing.mkXi; Ring_polynom.mkXi; Ring_polynom.mkZmon;
       Ring_polynom.mkZmon_ok; EnvRing.mk_X; Ring_polynom.mk_X; Tauto.mk_and;
       ZMicromega.mk_eq_pos; Tauto.mk_iff; Tauto.mk_iff_is_bool; Tauto.mk_impl;
       Ring_polynom.mk_monpol_list; Tauto.mk_or; Ring_polynom.mkadd_mult;
       Ring_polynom.mkadd_mult_ok; ZifyClasses.mkapp; ZifyClasses.mkapp2;
       Ring_polynom.mkmult1; Ring_polynom.mkmult1_ok; Ring_polynom.mkmult_c;
       Ring_polynom.mkmult_c_ok; Ring_polynom.mkmult_c_pos;
       Ring_polynom.mkmult_c_pos_ok; Ring_polynom.mkmult_pow;
       Ring_polynom.mkmult_pow_ok; Ring_polynom.mkmult_rec;
       Ring_polynom.mkmult_rec_ok; Ring_polynom.mkmultm1;
       Ring_polynom.mkmultm1_ok; Ring_polynom.mkopp_pow;
       Ring_polynom.mkopp_pow_ok; Ring_polynom.mkpow; Ring_polynom.mkpow_ok;
       ZifyClasses.mkrel; BinInt.Z.mod_eq; BinInt.Z.mod_mul;
       BinInt.Z.mod_neg_bound; BinInt.Z.mod_pos_bound; BinInt.Z.modulo;
       Ring_polynom.mon_of_pol; Ring_polynom.mon_of_pol_ok; Ring_theory.morph0;
       Ring_theory.morph1; Ring_theory.morph_add; Ring_theory.morph_eq;
       Ring_theory.morph_mul; Ring_theory.morph_opp; Ring_theory.morph_sub;
       Nat.mul; BinNat.N.mul; BinPos.Pos.mul; BinInt.Z.mul; BinNat.N.mul_0_l;
       BinInt.Z.mul_0_l; BinNat.N.mul_0_r; BinInt.Z.Private_BootStrap.mul_0_r;
       BinInt.Z.mul_0_r; BinPos.Pos.mul_1_l;
       BinInt.Z.Private_BootStrap.mul_1_l; BinInt.Z.mul_1_l;
       BinPos.Pos.mul_1_r; BinInt.Z.mul_1_r; BinPos.Pos.mul_add_distr_l;
       BinInt.Z.mul_add_distr_l; BinInt.Z.Private_BootStrap.mul_add_distr_pos;
       BinPos.Pos.mul_add_distr_r; BinInt.Z.Private_BootStrap.mul_add_distr_r;
       BinInt.Z.mul_add_distr_r; BinPos.Pos.mul_assoc; BinInt.Z.mul_assoc;
       BinInt.Z.mul_cancel_l; BinInt.Z.mul_cancel_r; BinNat.N.mul_comm;
       BinPos.Pos.mul_comm; BinInt.Z.mul_comm; BinPos.Pos.mul_compare_mono_l;
       BinPos.Pos.mul_compare_mono_r; BinInt.Z.mul_div_le; BinInt.Z.mul_eq_0;
       Rlimit.mul_factor; Rlimit.mul_factor_gt; Rlimit.mul_factor_gt_f;
       Rlimit.mul_factor_wd; BinInt.Z.mul_id_l; BinPos.Pos.mul_le_mono_l;
       BinInt.Z.mul_le_mono_nonneg; BinInt.Z.mul_le_mono_nonneg_l;
       BinInt.Z.mul_le_mono_nonneg_r; BinInt.Z.mul_le_mono_nonpos_l;
       BinInt.Z.mul_le_mono_nonpos_r; BinInt.Z.mul_le_mono_pos_l;
       BinInt.Z.mul_le_mono_pos_r; BinPos.Pos.mul_lt_mono_l;
       BinInt.Z.mul_lt_mono_neg_l; BinInt.Z.mul_lt_mono_neg_r;
       BinInt.Z.mul_lt_mono_nonneg; BinInt.Z.mul_lt_mono_pos_l;
       BinInt.Z.mul_lt_mono_pos_r; BinPos.Pos.mul_lt_mono_r;
       BinInt.Z.mul_lt_pred; BinInt.Z.mul_neg_neg; BinInt.Z.mul_neg_pos;
       BinInt.Z.mul_nonneg_nonneg; BinInt.Z.mul_nonneg_nonpos;
       BinInt.Z.mul_opp_comm; BinInt.Z.mul_opp_l; BinInt.Z.mul_opp_opp;
       BinInt.Z.Private_BootStrap.mul_opp_r; BinInt.Z.mul_opp_r;
       BinInt.Z.mul_pos_cancel_l; BinInt.Z.mul_pos_neg; BinInt.Z.mul_pos_pos;
       BinInt.Z.mul_reg_r; BinInt.Z.mul_shuffle0; BinInt.Z.mul_shuffle1;
       BinPos.Pos.mul_sub_distr_l; BinPos.Pos.mul_sub_distr_r;
       BinNat.N.mul_succ_l; BinPos.Pos.mul_succ_l; BinInt.Z.mul_succ_l;
       BinNat.N.mul_succ_r; BinPos.Pos.mul_succ_r; BinInt.Z.mul_succ_r;
       BinNat.N.mul_wd; BinInt.Z.mul_wd; BinPos.Pos.mul_xI_r;
       BinPos.Pos.mul_xO_r; RIneq.mult_IPR; RIneq.mult_IZR;
       Ring_polynom.mult_dev; Ring_polynom.mult_dev_ok; Ranalysis1.mult_fct;
       ZMicromega.narrow_interval_lower_bound; Znat.nat_N_Z;
       Compare_dec.nat_compare_ge; Compare_dec.nat_compare_le;
       Compare_dec.nat_compare_lt; nat_ind; nat_rec; nat_rect; RIneq.neg;
       BinInt.Pos2Z.neg_is_neg; ZMicromega.negate; ZMicromega.negate_correct;
       negb; Bool.negb_false_iff; Bool.negb_true_iff; Rtopology.neighbourhood;
       PeanoNat.Nat.neq_0_lt_0; RelationClasses.neq_Symmetric;
       BinPos.Pos.Private_Tac.neq_eq; BinInt.Z.Private_OrderTac.Tac.neq_eq;
       BinNat.N.neq_succ_0; PeanoNat.Nat.neq_succ_0; BinNat.N.neq_succ_diag_l;
       PeanoNat.Nat.neq_succ_diag_l; BinInt.Z.neq_succ_diag_l;
       BinInt.Z.Private_OrderTac.Tac.neq_sym; BinInt.Z.neq_sym;
       ZMicromega.nformula_of_cutting_plane;
       RingMicromega.nformula_plus_nformula;
       RingMicromega.nformula_plus_nformula_correct;
       RingMicromega.nformula_times_nformula;
       RingMicromega.nformula_times_nformula_correct; BinInt.Z.nle_gt;
       BinNat.N.nle_succ_diag_l; PeanoNat.Nat.nle_succ_diag_l;
       BinInt.Z.nle_succ_diag_l; PeanoNat.Nat.nlt_0_r; BinPos.Pos.nlt_1_r;
       BinInt.Z.nlt_ge; BinNat.N.nlt_succ_diag_l; PeanoNat.Nat.nlt_succ_diag_l;
       BinInt.Z.nlt_succ_diag_l; Ranalysis1.no_cond; RingMicromega.norm;
       ZMicromega.normZ; EnvRing.norm_aux; Ring_polynom.norm_aux;
       EnvRing.norm_aux_PEadd; Ring_polynom.norm_aux_PEadd;
       EnvRing.norm_aux_PEopp; Ring_polynom.norm_aux_PEopp;
       EnvRing.norm_aux_spec; Ring_polynom.norm_aux_spec;
       Ring_polynom.norm_subst; Ring_polynom.norm_subst_ok;
       Ring_polynom.norm_subst_spec; RingMicromega.normalise;
       ZMicromega.normalise; ZMicromega.normalise_correct;
       RingMicromega.normalise_sound; not; RIneq.not_0_IZR;
       ZArith_dec.not_Zeq_inf; Classical_Pred_Type.not_all_ex_not;
       Classical_Pred_Type.not_all_not_ex; Classical_Prop.not_and_or;
       not_eq_sym; Classical_Pred_Type.not_ex_all_not;
       BinPos.Pos.Private_Tac.not_ge_lt;
       BinNat.N.Private_OrderTac.Tac.not_ge_lt;
       PeanoNat.Nat.Private_OrderTac.Tac.not_ge_lt;
       BinInt.Z.Private_OrderTac.Tac.not_ge_lt;
       PeanoNat.Nat.Private_Tac.not_gt_le; BinPos.Pos.Private_Tac.not_gt_le;
       Qminmax.Q.Private_Tac.not_gt_le; BinInt.Z.Private_Tac.not_gt_le;
       BinNat.N.Private_OrderTac.Tac.not_gt_le;
       PeanoNat.Nat.Private_OrderTac.Tac.not_gt_le;
       BinInt.Z.Private_OrderTac.Tac.not_gt_le;
       Morphisms_Prop.not_iff_morphism;
       Morphisms_Prop.not_iff_morphism_obligation_1;
       Classical_Prop.not_imply_elim; Classical_Prop.not_imply_elim2;
       BinPos.Pos.Private_Tac.not_neq_eq;
       BinInt.Z.Private_OrderTac.Tac.not_neq_eq; Bool.not_true_iff_false;
       BinList.nth; Env.nth; List.nth; List.nth_in_or_default;
       BinList.nth_jump; Env.nth_jump; BinList.nth_pred_double;
       Env.nth_pred_double; Env.nth_spec; Field_theory.num; BinInt.Z.of_N;
       BinNat.N.of_nat; BinPos.Pos.of_nat; BinInt.Z.of_nat;
       BinPos.Pos.of_nat_succ; BinPos.Pos.of_succ_nat; BinInt.Z.one_succ;
       Rtopology.open_set; Rtopology.open_set_P1; Rtopology.open_set_P4;
       Rtopology.open_set_P6; BinInt.Z.opp; BinInt.Z.opp_0; RIneq.opp_IZR;
       BinInt.Z.Private_BootStrap.opp_add_distr; BinInt.Z.opp_add_distr;
       Ranalysis1.opp_fct; BinInt.Z.Private_BootStrap.opp_inj;
       BinInt.Z.opp_inj; BinInt.Z.opp_inj_wd;
       ConstructiveCauchyReals.opp_inject_Q; BinInt.Z.opp_involutive;
       BinInt.Z.opp_le_mono; BinInt.Z.opp_lt_mono; BinInt.Z.opp_nonneg_nonpos;
       BinInt.Z.opp_nonpos_nonneg; BinInt.Pos2Z.opp_pos; BinInt.Z.opp_pred;
       BinInt.Z.opp_sub_distr; BinInt.Z.opp_succ; BinInt.Z.opp_wd; or_cancel_r;
       Tauto.or_clause; Tauto.or_clause_cnf; Tauto.or_clause_cnf_correct;
       Tauto.or_clause_correct; Tauto.or_cnf; Tauto.or_cnf_correct;
       Tauto.or_cnf_opt; Tauto.or_cnf_opt_cnf_ff; Tauto.or_cnf_opt_cnf_ff_r;
       Tauto.or_cnf_opt_correct; or_comm; or_iff_compat_r;
       Morphisms_Prop.or_iff_morphism;
       Morphisms_Prop.or_iff_morphism_obligation_1; or_ind; orb; Bool.orb_comm;
       Bool.orb_true_iff; BinInt.Z.order_induction; BinInt.Z.order_induction_0;
       RingMicromega.padd; ZMicromega.padd; BinPos.Pos.peano_ind;
       BinInt.Z.peano_ind; BinNat.N.peano_rect; BinPos.Pos.peano_rect;
       Morphisms.per_partial_app_morphism;
       Morphisms.per_partial_app_morphism_obligation_1;
       RingMicromega.pexpr_times_nformula;
       RingMicromega.pexpr_times_nformula_correct; Ring_theory.phi_ext1_Proper;
       RIneq.plus_IPR; RIneq.plus_IZR; RIneq.plus_IZR_NEG_POS; plus_Sn_m;
       plus_n_O; plus_n_Sm; Rtopology.point_adherent;
       Morphisms.pointwise_relation; QMicromega.pop2_bop2;
       RMicromega.pop2_bop2; ZMicromega.pop2_bop2; RingMicromega.popp;
       ZMicromega.popp; RIneq.pos; BinNat.N.pos_div_eucl;
       BinInt.Z.pos_div_eucl; BinInt.Z.pos_div_eucl_bound;
       BinInt.Z.pos_div_eucl_eq; BinNat.N.pos_div_eucl_spec;
       BinInt.Pos2Z.pos_is_pos; BinInt.Pos2Z.pos_le_pos; BinInt.Z.pos_sub;
       BinInt.Z.Private_BootStrap.pos_sub_add; BinInt.Z.pos_sub_diag;
       BinInt.Z.pos_sub_discr; BinInt.Z.pos_sub_gt; BinInt.Z.pos_sub_lt;
       BinInt.Z.pos_sub_opp; BinInt.Z.pos_sub_spec; Znat.positive_N_nat;
       BinNums.positive_ind; Znat.positive_nat_Z; BinNums.positive_rec;
       BinNums.positive_rect; Rpow_def.pow; BinPos.Pos.pow; BinInt.Z.pow;
       BinInt.Z.pow_0_r; BinInt.Z.pow_1_l; BinPos.Pos.pow_1_r;
       BinInt.Z.pow_1_r; Ring_theory.pow_N; Field_theory.pow_N_ext;
       Ring_theory.pow_N_pow_N; Ring_theory.pow_N_th; BinInt.Z.pow_add_r;
       Field_theory.pow_ext; BinInt.Z.pow_gt_1; BinInt.Z.pow_le_mono_r;
       BinInt.Z.pow_lt_mono_l; BinInt.Z.pow_lt_mono_r; BinInt.Z.pow_neg_r;
       BinInt.Z.pow_nonneg; Ring_theory.pow_pos; BinInt.Z.pow_pos;
       Field_theory.pow_pos_0; Field_theory.pow_pos_1; EnvRing.pow_pos_add;
       Ring_polynom.pow_pos_add; Ring_theory.pow_pos_add;
       Field_theory.pow_pos_add_r; Field_theory.pow_pos_cst;
       Field_theory.pow_pos_div; Field_theory.pow_pos_mul_l;
       Field_theory.pow_pos_mul_r; BinInt.Z.pow_pos_nonneg;
       Field_theory.pow_pos_nz; Ring_theory.pow_pos_succ;
       Ring_theory.pow_pos_swap; BinPos.Pos.pow_succ_r; BinInt.Z.pow_succ_r;
       BinInt.Z.pow_twice_r; BinInt.Z.pow_wd; Rfunctions.powerRZ;
       Ranalysis1.pr_nu; Ranalysis4.pr_nu_var; PeanoNat.Nat.pred;
       BinNat.N.pred; BinPos.Pos.pred; BinInt.Z.pred; BinNat.N.pred_0;
       PeanoNat.Nat.pred_0; BinPos.Pos.pred_N; BinPos.Pos.pred_N_succ;
       BinPos.Pos.pred_double; BinInt.Z.pred_double;
       BinPos.Pos.pred_double_succ; BinInt.Z.pred_inj; BinInt.Z.pred_inj_wd;
       BinPos.Pos.pred_mask; BinNat.N.pred_succ; PeanoNat.Nat.pred_succ;
       BinInt.Z.pred_succ; BinNat.N.pred_wd; PeanoNat.Nat.pred_wd;
       BinInt.Z.pred_wd; PeanoNat.Nat.pred_wd_obligation_1; prod_ind;
       prod_rect; proj1; proj1_sig; proj2; proj2_sig;
       Rtopology.prolongement_C0; Rlimit.prop_eps; Morphisms.proper_prf;
       Morphisms.proper_sym_impl_iff; RingMicromega.psub; ZMicromega.psub;
       RingMicromega.psubC; QMicromega.qdeduce; QMicromega.qunsat;
       BinInt.Z.quotrem; BinInt.Z.quotrem_eq; Ring_polynom.r_list_pow;
       Ring_polynom.r_list_pow_rev; Field_theory.radd_ext;
       Ring_theory.radd_ext2_Proper; InitialRing.radd_ext3_Proper;
       InitialRing.radd_ext4_Proper; EnvRing.radd_ext_Proper;
       Field_theory.radd_ext_Proper; InitialRing.radd_ext_Proper;
       Ring_polynom.radd_ext_Proper; RMicromega.rdeduce; Field_theory.rdiv1;
       Field_theory.rdiv2b; Field_theory.rdiv3b; Field_theory.rdiv4;
       Field_theory.rdiv4b; Field_theory.rdiv5; Field_theory.rdiv6;
       Field_theory.rdiv7; Field_theory.rdiv7b; Field_theory.rdiv_ext;
       Field_theory.rdiv_r_r; Field_theory.rdiv_simpl;
       Morphisms.reflexive_eq_dom_reflexive; Morphisms.reflexive_proper;
       CMorphisms.reflexive_proper_proxy; Morphisms.reflexive_proper_proxy;
       Morphisms.reflexive_reflexive_proxy; RelationClasses.reflexivity;
       ConstructiveEpsilon.rel_ls_ind; ConstructiveEpsilon.rel_ls_post;
       Relation_Definitions.relation; CMorphisms.respectful;
       Morphisms.respectful; Rtopology.restriction_family; List.rev';
       List.rev_append; ZifyClasses.rew_iff; ZifyClasses.rew_iff_rev;
       Morphisms.rewrite_relation_eq_dom; BinNat.N.right_induction;
       PeanoNat.Nat.right_induction; BinInt.Z.right_induction;
       Ring_polynom.ring_correct; Ring_polynom.ring_rw_correct;
       Ring_polynom.ring_rw_pow_correct; Ring_tac.ring_subst_niter;
       Field_theory.rinv_ext_Proper; OrderedRing.rle_morph_Proper;
       RingMicromega.rle_morph_Proper; OrderedRing.rlt_morph_Proper;
       RingMicromega.rlt_morph_Proper; OrderedRing.rminus_morph;
       OrderedRing.rminus_morph_Proper; RingMicromega.rminus_morph_Proper;
       Field_theory.rmul_ext; Ring_theory.rmul_ext2_Proper;
       InitialRing.rmul_ext3_Proper; InitialRing.rmul_ext4_Proper;
       EnvRing.rmul_ext_Proper; Field_theory.rmul_ext_Proper;
       InitialRing.rmul_ext_Proper; Ring_polynom.rmul_ext_Proper;
       Field_theory.rmul_reg_l; Ring_theory.ropp_ext2_Proper;
       InitialRing.ropp_ext3_Proper; EnvRing.ropp_ext_Proper;
       Field_theory.ropp_ext_Proper; Ring_polynom.ropp_ext_Proper;
       OrderedRing.ropp_morph_Proper; RingMicromega.ropp_morph_Proper;
       Field_theory.ropp_neq_0; OrderedRing.rplus_morph_Proper;
       RingMicromega.rplus_morph_Proper; Ring_theory.rpow_pow_N;
       Field_theory.rsplit_common; Field_theory.rsplit_left;
       Field_theory.rsplit_right; Field_theory.rsub_0_l; Field_theory.rsub_0_r;
       EnvRing.rsub_ext_Proper; Field_theory.rsub_ext_Proper;
       Ring_polynom.rsub_ext_Proper; OrderedRing.rtimes_morph_Proper;
       RingMicromega.rtimes_morph_Proper; Tauto.rtyp; RMicromega.runsat;
       InitialRing.same_gen; InitialRing.same_genN; InitialRing.same_genZ;
       ConstructiveCauchyReals.scale; ConstructiveCauchyReals.seq;
       ConstructiveRcomplete.seq_cv; BinInt.Z.sgn;
       ClassicalDedekindReals.sig_forall_dec; ConstructiveLUB.sig_forall_dec_T;
       sig_ind; ConstructiveLUB.sig_lub; ClassicalDedekindReals.sig_not_dec;
       ConstructiveLUB.sig_not_dec_T; sig_rec; sig_rect; Ring_theory.sign_spec;
       Rlimit.single_limit; BinPos.Pos.size_nat; BinPos.Pos.size_nat_monotone;
       snd; OrderedRing.sor_setoid; OrderedRing.sor_setoid_Reflexive;
       OrderedRing.sor_setoid_Symmetric; OrderedRing.sor_setoid_Transitive;
       Field_theory.split; Field_theory.split_aux; Field_theory.split_aux_ok;
       Field_theory.split_aux_ok1; Field_theory.split_nz_l;
       Field_theory.split_nz_r; Field_theory.split_ok_l;
       Field_theory.split_ok_r; BinInt.Z.strong_left_induction;
       BinNat.N.strong_right_induction; PeanoNat.Nat.strong_right_induction;
       BinInt.Z.strong_right_induction; BinNat.N.sub; BinPos.Pos.sub;
       BinInt.Z.sub; BinInt.Z.sub_0_l; BinNat.N.sub_0_r; BinInt.Z.sub_0_r;
       BinInt.Z.sub_1_r; BinNat.N.sub_add; BinPos.Pos.sub_add;
       BinPos.Pos.sub_add_distr; BinInt.Z.sub_cancel_r; BinPos.Pos.sub_decr;
       BinNat.N.sub_diag; BinInt.Z.sub_diag; BinNat.N.sub_gt;
       BinInt.Z.sub_le_mono_r; BinInt.Z.sub_lt_mono_r; BinPos.Pos.sub_mask;
       BinPos.Pos.sub_mask_add; BinPos.Pos.sub_mask_add_diag_l;
       BinPos.Pos.sub_mask_add_diag_r; BinPos.Pos.sub_mask_carry;
       BinPos.Pos.sub_mask_carry_spec; BinPos.Pos.sub_mask_diag;
       BinPos.Pos.sub_mask_neg_iff; BinPos.Pos.sub_mask_nul_iff;
       BinPos.Pos.sub_mask_pos; BinPos.Pos.sub_mask_pos';
       BinPos.Pos.sub_mask_pos_iff; BinPos.Pos.sub_mask_spec;
       BinPos.Pos.sub_mask_succ_r; BinInt.Z.sub_move_0_r; BinInt.Z.sub_move_r;
       BinInt.Z.sub_opp_r; BinInt.Z.sub_simpl_r; BinPos.Pos.sub_sub_distr;
       BinInt.Z.sub_sub_distr; BinNat.N.sub_succ; BinInt.Z.sub_succ_l;
       BinNat.N.sub_succ_r; BinInt.Z.sub_succ_r; BinNat.N.sub_wd;
       BinInt.Z.sub_wd; BinPos.Pos.sub_xI_xI; BinPos.Pos.sub_xI_xO;
       BinPos.Pos.sub_xO_xI; BinPos.Pos.sub_xO_xO; Rtopology.subfamily;
       CRelationClasses.subrelation; RelationClasses.subrelation;
       CMorphisms.subrelation_proper; Morphisms.subrelation_proper;
       CMorphisms.subrelation_refl; Morphisms.subrelation_refl;
       CMorphisms.subrelation_respectful; Morphisms.subrelation_respectful;
       BinNat.N.succ; BinPos.Pos.succ; BinInt.Z.succ; RIneq.succ_IPR;
       BinNat.N.succ_double; BinInt.Z.succ_double; BinNat.N.succ_double_add;
       BinPos.Pos.succ_double_mask; BinNat.N.succ_double_mul;
       BinInt.Z.succ_double_spec; BinNat.N.succ_inj; PeanoNat.Nat.succ_inj;
       BinPos.Pos.succ_inj; BinInt.Z.succ_inj; BinNat.N.succ_inj_wd;
       PeanoNat.Nat.succ_inj_wd; BinInt.Z.succ_inj_wd;
       PeanoNat.Nat.succ_le_mono; BinInt.Z.succ_le_mono;
       PeanoNat.Nat.succ_lt_mono; BinPos.Pos.succ_lt_mono;
       BinInt.Z.succ_lt_mono; BinPos.Pos.succ_not_1; BinInt.Z.succ_pred;
       BinPos.Pos.succ_pred_double; BinPos.Pos.succ_pred_or; BinNat.N.succ_wd;
       PeanoNat.Nat.succ_wd; BinInt.Z.succ_wd;
       PeanoNat.Nat.succ_wd_obligation_1; sumbool_rec; sumbool_rect;
       RMicromega.sumboolb; BinPos.Pos.switch_Eq; CRelationClasses.symmetry;
       RelationClasses.symmetry; Env.tail; Tauto.tauto_checker;
       Tauto.tauto_checker_sound; List.tl; BinInt.Z.to_N; BinNat.N.to_nat;
       BinPos.Pos.to_nat; BinInt.Z.to_nat; BinInt.Z.to_pos;
       Rdefinitions.total_order_T; PeanoNat.Nat.Private_Tac.trans;
       BinPos.Pos.Private_Tac.trans; Qminmax.Q.Private_Tac.trans;
       BinInt.Z.Private_Tac.trans; BinNat.N.Private_OrderTac.Tac.trans;
       PeanoNat.Nat.Private_OrderTac.Tac.trans;
       BinInt.Z.Private_OrderTac.Tac.trans;
       Morphisms.trans_co_eq_inv_impl_morphism;
       Morphisms.trans_co_eq_inv_impl_morphism_obligation_1;
       Morphisms.trans_co_impl_morphism;
       Morphisms.trans_co_impl_morphism_obligation_1;
       CMorphisms.trans_contra_inv_impl_type_morphism;
       CMorphisms.trans_contra_inv_impl_type_morphism_obligation_1;
       OrdersTac.trans_ord; Morphisms.trans_sym_co_inv_impl_morphism;
       Morphisms.trans_sym_co_inv_impl_morphism_obligation_1;
       CRelationClasses.transitivity; RelationClasses.transitivity;
       InitialRing.triv_div; InitialRing.triv_div_th; BinInt.Z.two_succ;
       Ranalysis1.uniqueness_limite; Ranalysis1.uniqueness_step1;
       Ranalysis1.uniqueness_step2; Ranalysis1.uniqueness_step3;
       ZMicromega.valid_cut_sign; well_founded; well_founded_ind;
       well_founded_induction; well_founded_induction_type;
       Wf_nat.well_founded_ltof; BinPos.Pos.xI_succ_xO; Tauto.xcnf;
       Tauto.xcnf_correct; Tauto.xcnf_iff; Tauto.xcnf_impl;
       RingMicromega.xnegate; ZMicromega.xnegate;
       RingMicromega.xnegate_correct; ZMicromega.xnegate_correct;
       ZMicromega.xnnormalise; ZMicromega.xnnormalise_correct;
       RingMicromega.xnormalise; ZMicromega.xnormalise;
       RingMicromega.xnormalise_correct; ZMicromega.xnormalise_correct;
       Tauto.xor_clause_cnf; RMicromega.z_of_exp; Ring_polynom.zmon_pred;
       Ring_polynom.zmon_pred_ok; Acc; BoolSpec; ConstructiveCauchyReals.CReal;
       CompareSpec; CompareSpecT; ConstructiveReals.ConstructiveReals;
       ConstructiveLUB.DedekindDecCut; SetoidTactics.DefaultRelation;
       CRelationClasses.Equivalence; RelationClasses.Equivalence;
       Field_theory.FExpr; False; RingMicromega.Formula; Tauto.GFormula;
       ZifyClasses.InjTyp; Rlimit.Metric_Space; Ring_polynom.Mon; BinNums.N;
       RingMicromega.Op1; RingMicromega.Op2; RelationClasses.PER;
       EnvRing.PExpr; Ring_polynom.PExpr; EnvRing.Pol; Ring_polynom.Pol;
       RelationClasses.PreOrder; RingMicromega.Psatz; QArith_base.Q;
       RMicromega.Rcst; RelationClasses.RewriteRelation; OrderedRing.SOR;
       RingMicromega.SORaddon; RelationClasses.StrictOrder;
       BinPos.Pos.SubMaskSpec; True; BinNums.Z; ZMicromega.ZArithProof;
       ZMicromega.Zdivide_pol; Znumtheory.Zis_gcd;
       Field_theory.almost_field_theory; Ring_theory.almost_ring_theory; and;
       ConstructiveEpsilon.before_witness; bool; comparison;
       Ring_theory.div_theory; eq; ex; Rtopology.family;
       Field_theory.field_theory; Tauto.kind; le; Field_theory.linear; list;
       BinPos.Pos.mask; nat; RIneq.negreal; option; or; OrdersTac.ord;
       BinNums.positive; RIneq.posreal; Ring_theory.power_theory; prod;
       Bool.reflect; ConstructiveEpsilon.rel_ls; Ring_theory.ring_eq_ext;
       Ring_theory.ring_morph; Ring_theory.ring_theory; Field_theory.rsplit;
       Ring_theory.semi_morph; Ring_theory.semi_ring_theory; sig; sigT;
       Ring_theory.sign_theory; Ring_theory.sring_eq_ext; sum; sumbool; sumor;
       VarMap.t; unit; Acc_intro; BoolSpecT; ConstructiveCauchyReals.mkCReal;
       CompEq; CompEqT; ConstructiveReals.Build_ConstructiveReals;
       ConstructiveLUB.Build_DedekindDecCut;
       SetoidTactics.Build_DefaultRelation; CRelationClasses.Build_Equivalence;
       RelationClasses.Build_Equivalence; Field_theory.FEO;
       RingMicromega.Build_Formula; Tauto.TT; ZifyClasses.mkinj;
       Rlimit.Build_Metric_Space; Ring_polynom.mon0; BinNums.N0;
       RingMicromega.Equal; RingMicromega.OpEq; RelationClasses.Build_PER;
       EnvRing.PEc; Ring_polynom.PEO; EnvRing.Pc; Ring_polynom.Pc;
       RelationClasses.Build_PreOrder; RingMicromega.PsatzLet;
       QArith_base.Qmake; RMicromega.C0; RelationClasses.Build_RewriteRelation;
       OrderedRing.mk_SOR_theory; RingMicromega.mk_SOR_addon;
       RelationClasses.Build_StrictOrder; BinPos.Pos.SubIsNul; I; BinNums.Z0;
       ZMicromega.DoneProof; ZMicromega.Zdiv_Pc; Znumtheory.Zis_gcd_intro;
       Field_theory.mk_afield; Ring_theory.mk_art; conj;
       ConstructiveEpsilon.stop; true; Eq; Ring_theory.mkdiv_th; eq_refl;
       ex_intro; Rtopology.mkfamily; Field_theory.mk_field; Tauto.isProp; le_n;
       Field_theory.mk_linear; nil; BinPos.Pos.IsNul; O; RIneq.mknegreal; Some;
       or_introl; OrdersTac.OEQ; BinNums.xI; RIneq.mkposreal;
       Ring_theory.mkpow_th; pair; Bool.ReflectT; ConstructiveEpsilon.Rstop;
       Ring_theory.mk_reqe; Ring_theory.mkmorph; Ring_theory.mk_rt;
       Field_theory.mk_rsplit; Ring_theory.mkRmorph; Ring_theory.mk_srt; exist;
       existT; Ring_theory.mksign_th; Ring_theory.mk_seqe; inl; left; inleft;
       VarMap.Empty; tt; BoolSpecF; CompLt; CompLtT; Field_theory.FEI;
       Tauto.FF; Ring_polynom.zmon; BinNums.Npos; RingMicromega.NonEqual;
       RingMicromega.OpNEq; EnvRing.PEX; Ring_polynom.PEI; EnvRing.Pinj;
       Ring_polynom.Pinj; RingMicromega.PsatzIn; RMicromega.C1;
       BinPos.Pos.SubIsPos; BinNums.Zpos; ZMicromega.RatProof;
       ZMicromega.Zdiv_Pinj; ConstructiveEpsilon.next; false; Lt; Tauto.isBool;
       le_S; cons; BinPos.Pos.IsPos; S; None; or_intror; OrdersTac.OLT;
       BinNums.xO; Bool.ReflectF; ConstructiveEpsilon.Rnext; inr; right;
       inright; VarMap.Elt; CompGt; CompGtT; Field_theory.FEc; Tauto.X;
       Ring_polynom.vmon; RingMicromega.Strict; RingMicromega.OpLe;
       EnvRing.PEadd; Ring_polynom.PEc; EnvRing.PX; Ring_polynom.PX;
       RingMicromega.PsatzSquare; RMicromega.CQ; BinPos.Pos.SubIsNeg;
       BinNums.Zneg; ZMicromega.CutProof; ZMicromega.Zdiv_PX; Gt;
       BinPos.Pos.IsNeg; OrdersTac.OLE; BinNums.xH; VarMap.Branch;
       Field_theory.FEX; Tauto.A; RingMicromega.NonStrict; RingMicromega.OpGe;
       EnvRing.PEsub; Ring_polynom.PEX; RingMicromega.PsatzMulC; RMicromega.CZ;
       ZMicromega.SplitProof; Field_theory.FEadd; Tauto.AND;
       RingMicromega.OpLt; EnvRing.PEmul; Ring_polynom.PEadd;
       RingMicromega.PsatzMulE; RMicromega.CPlus; ZMicromega.EnumProof;
       Field_theory.FEsub; Tauto.OR; RingMicromega.OpGt; EnvRing.PEopp;
       Ring_polynom.PEsub; RingMicromega.PsatzAdd; RMicromega.CMinus;
       ZMicromega.ExProof; Field_theory.FEmul; Tauto.NOT; EnvRing.PEpow;
       Ring_polynom.PEmul; RingMicromega.PsatzC; RMicromega.CMult;
       Field_theory.FEopp; Tauto.IMPL; Ring_polynom.PEopp;
       RingMicromega.PsatzZ; RMicromega.CPow; Field_theory.FEinv; Tauto.IFF;
       Ring_polynom.PEpow; RMicromega.CInv; Field_theory.FEdiv; Tauto.EQ;
       RMicromega.COpp; Field_theory.FEpow;  }}
    Spilled_1 = 3375
    T = __TIME__
  Query assignments:
    S = {{ Nat.add; eq; nat; O;  }}
    Spilled_1 = 4
    T = prod `x` (global (indt «nat»)) c0 \
   app
    [global (indt «eq»), X0 c0, 
     app [global (const «Nat.add»), c0, global (indc «O»)], c0]
    _uvk_18_ = c0 \
  X0 c0
  Syntactic constraints:
   {c0} : decl c0 `x` (global (indt «nat»)) ?- evar (X0 c0) (X1 c0) (X0 c0)  /* suspended on X0 */
   {c0} : decl c0 `x` (global (indt «nat»))
     ?- evar (X2 c0) (sort (typ «test.test.30»)) (X1 c0)  /* suspended on X2, X1 */
  Universe constraints:
  UNIVERSES:
   {test.test.30} |= 
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   α8
  WEAK CONSTRAINTS:
   
  
  Query assignments:
    Decl = record Rec (sort (typ «test.test.31»)) BuildRec 
   (field [] f (sort (typ «test.test.32»)) c0 \ end-record)
    _uvk_27_ = «test.test.31»
    _uvk_28_ = «test.test.32»
  Universe constraints:
  UNIVERSES:
   {test.test.32 test.test.31} |= 
  ALGEBRAIC UNIVERSES:
   {test.test.32 test.test.31}
  FLEXIBLE UNIVERSES:
   test.test.32
   test.test.31
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Module
  Test
  := Struct
       Record Rec@{u u0} : Type@{u} := BuildRec
         { f : Type@{u0} }.
       (* u u0 |= u0 < u *)
       Definition f : Rec@{u u0} -> Type@{u0}.
         (* u u0 |= u0 < u *)
     End
  
  Test.f@{test.test.33
  test.test.34}
       : Test.Rec@{test.test.33 test.test.34} -> Type@{test.test.34}
  (* {test.test.34 test.test.33} |= test.test.34 < test.test.33 *)
  Query assignments:
    LP = «Coq.ZArith.Znat»
    MP = «Coq.ZArith.Znat.N2Z»
