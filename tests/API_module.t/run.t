  $ . ../setup-project.sh
  $ dune build test.vo
  File "dune", line 6, characters 0-42:
  6 | (coq.theory
  7 |  (name test)
  8 |  (theories elpi))
  Query assignments:
    L = [gref (indt «Empty_set»), gref (const «Empty_set_rect»), 
   gref (const «Empty_set_ind»), gref (const «Empty_set_rec»), 
   gref (const «Empty_set_sind»), gref (indt «unit»), 
   gref (const «unit_rect»), gref (const «unit_ind»), 
   gref (const «unit_rec»), gref (const «unit_sind»), 
   gref (indt «bool»), gref (const «bool_rect»), 
   gref (const «bool_ind»), gref (const «bool_rec»), 
   gref (const «bool_sind»), gref (const «andb»), gref (const «orb»), 
   gref (const «implb»), gref (const «xorb»), gref (const «negb»), 
   gref (const «andb_prop»), gref (const «andb_true_intro»), 
   gref (indt «eq_true»), gref (const «eq_true_rect»), 
   gref (const «eq_true_ind»), gref (const «eq_true_rec»), 
   gref (const «eq_true_sind»), gref (const «is_true»), 
   gref (const «eq_true_ind_r»), gref (const «eq_true_rec_r»), 
   gref (const «eq_true_rect_r»), gref (indt «BoolSpec»), 
   gref (const «BoolSpec_ind»), gref (const «BoolSpec_sind»), 
   gref (indt «nat»), gref (const «nat_rect»), gref (const «nat_ind»), 
   gref (const «nat_rec»), gref (const «nat_sind»), 
   gref (indt «option»), gref (const «option_rect»), 
   gref (const «option_ind»), gref (const «option_rec»), 
   gref (const «option_sind»), gref (const «option_map»), 
   gref (indt «sum»), gref (const «sum_rect»), gref (const «sum_ind»), 
   gref (const «sum_rec»), gref (const «sum_sind»), gref (indt «prod»), 
   gref (const «prod_rect»), gref (const «prod_ind»), 
   gref (const «prod_rec»), gref (const «prod_sind»), 
   gref (const «fst»), gref (const «snd»), 
   gref (const «surjective_pairing»), 
   gref (const «injective_projections»), gref (const «pair_equal_spec»), 
   gref (const «curry»), gref (const «uncurry»), 
   gref (const «rew_pair»), gref (indt «list»), 
   gref (const «list_rect»), gref (const «list_ind»), 
   gref (const «list_rec»), gref (const «list_sind»), 
   gref (const «length»), gref (const «app»), gref (indt «comparison»), 
   gref (const «comparison_rect»), gref (const «comparison_ind»), 
   gref (const «comparison_rec»), gref (const «comparison_sind»), 
   gref (const «comparison_eq_stable»), gref (const «CompOpp»), 
   gref (const «CompOpp_involutive»), gref (const «CompOpp_inj»), 
   gref (const «CompOpp_iff»), gref (indt «CompareSpec»), 
   gref (const «CompareSpec_ind»), gref (const «CompareSpec_sind»), 
   gref (indt «CompareSpecT»), gref (const «CompareSpecT_rect»), 
   gref (const «CompareSpecT_ind»), gref (const «CompareSpecT_rec»), 
   gref (const «CompareSpecT_sind»), gref (const «CompareSpec2Type»), 
   gref (const «CompSpec»), gref (const «CompSpecT»), 
   gref (const «CompSpec2Type»), gref (const «ID»), gref (const «id»), 
   gref (const «IDProp»), gref (const «idProp»)]
    MP = «Coq.Init.Datatypes»
  test.test.X.i
  File "./test.v", line 19, characters 0-1079:
  Error: The elpi tactic/command modules failed without giving a specific error
  message. Please report this inconvenience to the authors of the program.
  
  [1]
