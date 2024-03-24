  $ . ../setup-project.sh
  $ dune build test.vo
  ?r : Reflexive R
       : Reflexive R
  where
  ?r : [ |- Reflexive R]
  Query assignments:
    GR = const «myi»
  myi : Reflexive R
       : Reflexive R
  Query assignments:
    L = [tc-instance (const «relation_equivalence_rewrite_relation») 
    (tc-priority-computed 0), 
   tc-instance (const «iff_rewrite_relation») (tc-priority-given 2), 
   tc-instance (const «impl_rewrite_relation») (tc-priority-given 3), 
   tc-instance (const «inverse_impl_rewrite_relation») (tc-priority-given 3), 
   tc-instance (const «Equivalence_PER») (tc-priority-given 10), 
   tc-instance (const «relation_equivalence_equivalence») 
    (tc-priority-computed 0), 
   tc-instance (const «predicate_equivalence_equivalence») 
    (tc-priority-computed 0), 
   tc-instance (const «iff_equivalence») (tc-priority-computed 0), 
   tc-instance (const «eq_equivalence») (tc-priority-given 10), 
   tc-instance (const «relation_implication_preorder») 
    (tc-priority-computed 0), 
   tc-instance (const «predicate_implication_preorder») 
    (tc-priority-computed 0), 
   tc-instance (const «Equivalence_PreOrder») (tc-priority-given 10), 
   tc-instance (const «Bool.Decidable_eq_bool») (tc-priority-computed 0), 
   tc-instance (const «DecidableClass.Decidable_not») 
    (tc-priority-computed 1), 
   tc-instance (const «subrelation_partial_order») (tc-priority-computed 0), 
   tc-instance (const «iff_Transitive») (tc-priority-computed 0), 
   tc-instance (const «impl_Transitive») (tc-priority-computed 0), 
   tc-instance (const «eq_Transitive») (tc-priority-computed 0), 
   tc-instance (const «Equivalence_Transitive») (tc-priority-computed 1), 
   tc-instance (const «StrictOrder_Transitive») (tc-priority-computed 1), 
   tc-instance (const «PreOrder_Transitive») (tc-priority-given 2), 
   tc-instance (const «PER_Transitive») (tc-priority-given 3), 
   tc-instance (const «StrictOrder_Irreflexive») (tc-priority-computed 1), 
   tc-instance (const «StrictOrder_Asymmetric») (tc-priority-computed 1), 
   tc-instance (const «iff_Reflexive») (tc-priority-computed 0), 
   tc-instance (const «impl_Reflexive») (tc-priority-computed 0), 
   tc-instance (const «eq_Reflexive») (tc-priority-computed 0), 
   tc-instance (const «Equivalence_Reflexive») (tc-priority-computed 1), 
   tc-instance (const «PreOrder_Reflexive») (tc-priority-given 2), 
   tc-instance (const «myi») (tc-priority-given 10), 
   tc-instance (const «partial_order_antisym») (tc-priority-computed 2), 
   tc-instance (const «iff_Symmetric») (tc-priority-computed 0), 
   tc-instance (const «neq_Symmetric») (tc-priority-computed 0), 
   tc-instance (const «eq_Symmetric») (tc-priority-computed 0), 
   tc-instance (const «Equivalence_Symmetric») (tc-priority-computed 1), 
   tc-instance (const «PER_Symmetric») (tc-priority-given 3)]
  Query assignments:
    GR = indt «RewriteRelation»
    L = [tc-instance (const «relation_equivalence_rewrite_relation») 
    (tc-priority-computed 0), 
   tc-instance (const «iff_rewrite_relation») (tc-priority-given 2), 
   tc-instance (const «impl_rewrite_relation») (tc-priority-given 3), 
   tc-instance (const «inverse_impl_rewrite_relation») (tc-priority-given 3)]
  Query assignments:
    GR = indt «RewriteRelation»
  Query assignments:
    GR = indt «True»
  Query assignments:
    GR = const «myc»
  eq_op myc t t
       : bool
  Query assignments:
    L = [cs-instance (const «carrier») (cs-gref (const «W»)) (const «myc»), 
   cs-instance (const «eq_op») (cs-gref (const «Z»)) (const «myc»)]
  Query assignments:
    I = «eq»
    P1 = «carrier»
    P2 = «eq_op»
  Query assignments:
    GR = const «myc1»
  eq_op myc1 t1 t1
       : bool
  Query assignments:
    P = const «eq_op»
  Query assignments:
    W = const «W»
  [cs-instance (const «eq_op») (cs-gref (const «Z1»)) (const «myc1»)]
  Query assignments:
    L = [cs-instance (const «eq_op») (cs-gref (const «Z1»)) (const «myc1»)]
    P = const «eq_op»
    W = const «Z1»
  Query assignments:
    P = const «eq_op»
    W = indt «nat»
  Query assignments:
    C1 = const «C1»
    GR1 = const «c12»
    GR2 = const «c1t»
    GR3 = const «c1f»
  fun x : C1 => x : C2
       : C1 -> C2
  fun (x : C1) (_ : x) => true
       : forall x : C1, x -> bool
  fun x : C1 => x 3
       : C1 -> nat
  Query assignments:
    L = [coercion (const «c1t») 0 (const «C1») sortclass, 
   coercion (const «c1f») 0 (const «C1») funclass, 
   coercion (const «c12») 0 (const «C1») (grefclass (const «C2»)), 
   coercion (const «reverse_coercion») 3 (const «ReverseCoercionSource») 
    (grefclass (const «ReverseCoercionTarget»))]
  Query assignments:
    Spilled_1 = const «nuc»
  nuc : forall x : nat, C1 -> C3 x
  
  nuc is not universe polymorphic
  Arguments nuc x%nat_scope _
  nuc is a reversible coercion
  Expands to: Constant test.test.nuc
  File "./test.v", line 24, characters 0-30:
  Warning:
  There is an hint extern in the typeclass db: 
  (*external*) (equiv_rewrite_relation R)
  [TC.hints,elpi,default]
  File "./test.v", line 24, characters 0-30:
  Warning:
  There is an hint extern in the typeclass db: 
  (*external*) (class_apply @flip_StrictOrder)
  [TC.hints,elpi,default]
  File "./test.v", line 24, characters 0-30:
  Warning:
  There is an hint extern in the typeclass db: 
  (*external*) (class_apply @flip_PreOrder)
  [TC.hints,elpi,default]
  File "./test.v", line 24, characters 0-30:
  Warning:
  There is an hint extern in the typeclass db: 
  (*external*) (class_apply @PartialOrder_inverse)
  [TC.hints,elpi,default]
  File "./test.v", line 24, characters 0-30:
  Warning:
  There is an hint extern in the typeclass db: 
  (*external*) (class_apply @subrelation_symmetric)
  [TC.hints,elpi,default]
  File "./test.v", line 24, characters 0-30:
  Warning:
  There is an hint extern in the typeclass db: 
  (*external*) (class_apply @flip_Transitive)
  [TC.hints,elpi,default]
  File "./test.v", line 24, characters 0-30:
  Warning:
  There is an hint extern in the typeclass db: 
  (*external*) (class_apply @flip_Irreflexive)
  [TC.hints,elpi,default]
  File "./test.v", line 24, characters 0-30:
  Warning:
  There is an hint extern in the typeclass db: 
  (*external*) (class_apply @complement_Irreflexive)
  [TC.hints,elpi,default]
  File "./test.v", line 24, characters 0-30:
  Warning:
  There is an hint extern in the typeclass db: 
  (*external*) (class_apply @flip_Asymmetric)
  [TC.hints,elpi,default]
  File "./test.v", line 24, characters 0-30:
  Warning:
  There is an hint extern in the typeclass db: 
  (*external*) (class_apply @irreflexivity)
  [TC.hints,elpi,default]
  File "./test.v", line 24, characters 0-30:
  Warning:
  There is an hint extern in the typeclass db: 
  (*external*) (apply flip_Reflexive)
  [TC.hints,elpi,default]
  File "./test.v", line 24, characters 0-30:
  Warning:
  There is an hint extern in the typeclass db: 
  (*external*) unconvertible
  [TC.hints,elpi,default]
  File "./test.v", line 24, characters 0-30:
  Warning:
  There is an hint extern in the typeclass db: 
  (*external*) (class_apply @flip_Antisymmetric)
  [TC.hints,elpi,default]
  File "./test.v", line 24, characters 0-30:
  Warning:
  There is an hint extern in the typeclass db: 
  (*external*) (class_apply @flip_Symmetric)
  [TC.hints,elpi,default]
  File "./test.v", line 24, characters 0-30:
  Warning:
  There is an hint extern in the typeclass db: 
  (*external*) (class_apply @complement_Symmetric)
  [TC.hints,elpi,default]
  File "./test.v", line 25, characters 0-70:
  Warning:
  There is an hint extern in the typeclass db: 
  (*external*) (equiv_rewrite_relation R)
  [TC.hints,elpi,default]
