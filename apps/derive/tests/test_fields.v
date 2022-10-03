From elpi.apps Require Import derive.fields.

From elpi.apps.derive.tests Require Import test_derive_stdlib test_eqType_ast test_tag.
Import test_derive_stdlib.Coverage test_eqType_ast.Coverage test_tag.Coverage.

Module Coverage.
Elpi derive.fields empty.
Elpi derive.fields unit.
Elpi derive.fields peano.
Elpi derive.fields option.
Elpi derive.fields pair.
Elpi derive.fields seq.
Elpi derive.fields box_peano.
Elpi derive.fields rose.
Elpi derive.fields rose_p.
Elpi derive.fields rose_o.
Fail Elpi derive.fields nest.
Fail Elpi derive.fields w.
Fail Elpi derive.fields vect.
Fail Elpi derive.fields dyn.
Fail Elpi derive.fields zeta.
Elpi derive.fields beta.
Fail Elpi derive.fields iota.
Elpi derive.fields large.
Elpi derive.fields prim_int.
Fail Elpi derive.fields prim_float.
Elpi derive.fields fo_record.
Elpi derive.fields pa_record.
Elpi derive.fields pr_record.
Fail Elpi derive.fields dep_record.
Elpi derive.fields enum.
Elpi derive.fields bool.
Fail Elpi derive.fields eq.
Elpi derive.fields sigma_bool.
Elpi derive.fields ord.
Elpi derive.fields ord2.
Elpi derive.fields val.
End Coverage.

Import Coverage.
Import PArith.

Check empty_fields_t : positive -> Type. 
Check empty_fields : forall (n:empty), empty_fields_t (empty_tag n). 
Check empty_construct : forall (p: positive),  empty_fields_t p -> Datatypes.option empty.
Check empty_constructP : forall (n:empty), empty_construct (empty_tag n) (empty_fields n) = Datatypes.Some n.

Check unit_fields_t : positive -> Type. 
Check unit_fields : forall (n:unit), unit_fields_t (unit_tag n). 
Check unit_construct : forall (p: positive),  unit_fields_t p -> Datatypes.option unit.
Check unit_constructP : forall (n:unit), unit_construct (unit_tag n) (unit_fields n) = Datatypes.Some n.

Check peano_fields_t : positive -> Type. 
Check peano_fields : forall (n:peano), peano_fields_t (peano_tag n). 
Check peano_construct : forall (p: positive),  peano_fields_t p -> Datatypes.option peano.
Check peano_constructP : forall (n:peano), peano_construct (peano_tag n) (peano_fields n) = Datatypes.Some n.

Check option_fields_t : Type -> Numbers.BinNums.positive -> Type. 
Check option_fields : forall (A:Type) (l:option A), option_fields_t A (option_tag A l). 
Check option_construct : forall (A:Type) (p: Numbers.BinNums.positive),  option_fields_t A p -> Datatypes.option (option A).
Check option_constructP : forall (A:Type) (l:option A), option_construct A (option_tag A l) (option_fields A l) = Datatypes.Some l.

Check pair_fields_t : Type -> Type -> Numbers.BinNums.positive -> Type. 
Check pair_fields : forall (A B :Type) (l:pair A B), pair_fields_t A B (pair_tag A B l). 
Check pair_construct : forall (A B:Type) (p: Numbers.BinNums.positive),  pair_fields_t A B p -> Datatypes.option (pair A B).
Check pair_constructP : forall (A B:Type) (l:pair A B), pair_construct A B (pair_tag A B l) (pair_fields A B l) = Datatypes.Some l.

Check seq_fields_t : Type -> Numbers.BinNums.positive -> Type. 
Check seq_fields : forall (A:Type) (l:seq A), seq_fields_t A (seq_tag A l). 
Check seq_construct : forall (A:Type) (p: Numbers.BinNums.positive),  seq_fields_t A p -> Datatypes.option (seq A).
Check seq_constructP : forall (A:Type) (l:seq A), seq_construct A (seq_tag A l) (seq_fields A l) = Datatypes.Some l.

Check rose_fields_t : Type -> Numbers.BinNums.positive -> Type. 
Check rose_fields : forall (A:Type) (l:rose A), rose_fields_t A (rose_tag A l). 
Check rose_construct : forall (A:Type) (p: Numbers.BinNums.positive),  rose_fields_t A p -> Datatypes.option (rose A).
Check rose_constructP : forall (A:Type) (l:rose A), rose_construct A (rose_tag A l) (rose_fields A l) = Datatypes.Some l.

Fail Check nest_fields_t : Type -> Numbers.BinNums.positive -> Type. 
Fail Check nest_fields : forall (A:Type) (l:nest A), nest_fields_t A (nest_tag A l). 
Fail Check nest_construct : forall (A:Type) (p: Numbers.BinNums.positive),  nest_fields_t A p -> Datatypes.option (nest A).
Fail Check nest_constructP : forall (A:Type) (l:nest A), nest_construct A (nest_tag A l) (nest_fields A l) = Datatypes.Some l.

Fail Check w_fields_t : Type -> Numbers.BinNums.positive -> Type. 
Fail Check w_fields : forall (A:Type) (l:w A), w_fields_t A (w_tag A l). 
Fail Check w_construct : forall (A:Type) (p: Numbers.BinNums.positive),  w_fields_t A p -> Datatypes.option (w A).
Fail Check w_constructP : forall (A:Type) (l:w A), w_construct A (w_tag A l) (w_fields A l) = Datatypes.Some l.

Fail Check vect_fields_t : Type -> Numbers.BinNums.positive -> Type. 
Fail Check vect_fields : forall (A:Type) (l:vect A), vect_fields_t A (vect_tag A l). 
Fail Check vect_construct : forall (A:Type) (p: Numbers.BinNums.positive),  vect_fields_t A p -> Datatypes.option (vect A).
Fail Check vect_constructP : forall (A:Type) (l:vect A), vect_construct A (vect_tag A l) (vect_fields A l) = Datatypes.Some l.

Fail Check dyn_fields_t : positive -> Type. 
Fail Check dyn_fields : forall (n:dyn), dyn_fields_t (dyn_tag n). 
Fail Check dyn_construct : forall (p: positive),  dyn_fields_t p -> Datatypes.option dyn.
Fail Check dyn_constructP : forall (n:dyn), dyn_construct (dyn_tag n) (dyn_fields n) = Datatypes.Some n.

Fail Check zeta_fields_t : Type -> Numbers.BinNums.positive -> Type. 
Fail Check zeta_fields : forall (A:Type) (l:zeta A), zeta_fields_t A (zeta_tag A l). 
Fail Check zeta_construct : forall (A:Type) (p: Numbers.BinNums.positive),  zeta_fields_t A p -> option (zeta A).
Fail Check zeta_constructP : forall (A:Type) (l:zeta A), zeta_construct A (zeta_tag A l) (zeta_fields A l) = Some l.

Check beta_fields_t : Type -> Numbers.BinNums.positive -> Type. 
Check beta_fields : forall (A:Type) (l:beta A), beta_fields_t A (beta_tag A l). 
Check beta_construct : forall (A:Type) (p: Numbers.BinNums.positive),  beta_fields_t A p -> Datatypes.option (beta A).
Check beta_constructP : forall (A:Type) (l:beta A), beta_construct A (beta_tag A l) (beta_fields A l) = Datatypes.Some l.

Fail Check iota_fields_t : positive -> Type. 
Fail Check iota_fields : forall (n:iota), iota_fields_t (iota_tag n). 
Fail Check iota_construct : forall (p: positive),  iota_fields_t p -> Datatypes.option iota.
Fail Check iota_constructP : forall (n:iota), iota_construct (iota_tag n) (iota_fields n) = Datatypes.Some n.

Check large_fields_t : positive -> Type. 
Check large_fields : forall (n:large), large_fields_t (large_tag n). 
Check large_construct : forall (p: positive),  large_fields_t p -> Datatypes.option large.
Check large_constructP : forall (n:large), large_construct (large_tag n) (large_fields n) = Datatypes.Some n.

Check prim_int_fields_t : positive -> Type. 
Check prim_int_fields : forall (n:prim_int), prim_int_fields_t (prim_int_tag n). 
Check prim_int_construct : forall (p: positive),  prim_int_fields_t p -> Datatypes.option prim_int.
Check prim_int_constructP : forall (n:prim_int), prim_int_construct (prim_int_tag n) (prim_int_fields n) = Datatypes.Some n.

Fail Check prim_float_fields_t : positive -> Type. 
Fail Check prim_float_fields : forall (n:prim_float), prim_float_fields_t (prim_float_tag n). 
Fail Check prim_float_construct : forall (p: positive),  prim_float_fields_t p -> Datatypes.option prim_float.
Fail Check prim_float_constructP : forall (n:prim_float), prim_float_construct (prim_float_tag n) (prim_float_fields n) = Datatypes.Some n.

Check pa_record_fields_t : Type -> Numbers.BinNums.positive -> Type. 
Check pa_record_fields : forall (A:Type) (l:pa_record A), pa_record_fields_t A (pa_record_tag A l). 
Check pa_record_construct : forall (A:Type) (p: Numbers.BinNums.positive),  pa_record_fields_t A p -> Datatypes.option (pa_record A).
Check pa_record_constructP : forall (A:Type) (l:pa_record A), pa_record_construct A (pa_record_tag A l) (pa_record_fields A l) = Datatypes.Some l.

Check pr_record_fields_t : Type -> Numbers.BinNums.positive -> Type. 
Check pr_record_fields : forall (A:Type) (l:pr_record A), pr_record_fields_t A (pr_record_tag A l). 
Check pr_record_construct : forall (A:Type) (p: Numbers.BinNums.positive),  pr_record_fields_t A p -> Datatypes.option (pr_record A).
Check pr_record_constructP : forall (A:Type) (l:pr_record A), pr_record_construct A (pr_record_tag A l) (pr_record_fields A l) = Datatypes.Some l.

Check sigma_bool_fields_t :  Numbers.BinNums.positive -> Type. 
Check sigma_bool_fields : forall (l:sigma_bool), sigma_bool_fields_t (sigma_bool_tag l). 
Check sigma_bool_construct : forall (p: Numbers.BinNums.positive),  sigma_bool_fields_t p -> Datatypes.option sigma_bool.
Check sigma_bool_constructP : forall (l:sigma_bool), sigma_bool_construct (sigma_bool_tag l) (sigma_bool_fields l) = Datatypes.Some l.

Check ord_fields_t : peano -> Numbers.BinNums.positive -> Type.
Check ord_fields : forall (p:peano) (o:ord p), ord_fields_t p (ord_tag p o).
Check ord_construct : forall (n:peano) (p:Numbers.BinNums.positive), ord_fields_t n p -> Datatypes.option (ord n).
Check ord_constructP : forall (p:peano) (o:ord p), ord_construct p (ord_tag p o) (ord_fields p o) = Datatypes.Some o.

Check ord2_fields_t : peano -> Numbers.BinNums.positive -> Type.
Check ord2_fields : forall (p:peano) (o:ord2 p), ord2_fields_t p (ord2_tag p o).
Check ord2_construct : forall (n:peano) (p:Numbers.BinNums.positive), ord2_fields_t n p -> Datatypes.option (ord2 n).
Check ord2_constructP : forall (p:peano) (o:ord2 p), ord2_construct p (ord2_tag p o) (ord2_fields p o) = Datatypes.Some o.

Check val_fields_t : Numbers.BinNums.positive -> Type.
Check val_fields : forall i : val, val_fields_t (val_tag i).
Check val_construct : forall (p: Numbers.BinNums.positive),  val_fields_t p -> Datatypes.option val.
Check val_constructP : forall (v:val), val_construct (val_tag v) (val_fields v) = Datatypes.Some v.

