import LeanQEC.ComputerAlgebra.BitVecSAT
import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide
import LeanQEC.ComputerAlgebra.BitVecCorrectness
import LeanQEC.Stabilizer.BB
import LeanQEC.Stabilizer.BitVecSATToDist
set_option maxRecDepth 9999999
def BB72_A :=
  let l := 6
  let m := 6
  BB3_matrix l m (true, 3) (false, 1) (false, 2)
def BB72_B :=
  let l := 6
  let m := 6
  BB3_matrix l m (true, 1) (true, 2) (false, 3)
def BB72_X_mat := BB72_A.hstack_fin BB72_B
def BB72_Z_mat := BB72_B.transpose.hstack_fin BB72_A.transpose
def BB72_X : BitVec (36 * 72) := 0x1000008200c0020000080000410840010000040000208c0000800080000010460000400040000008230000200020000004118000100080400002000300080040200001002100040020100000803000020012000000401800010009000000200c0000800480000010060000408201000000000c0020410080000000840010208040000000c0000810480000000060000408240000000030000204120000000018000102080400080000300001040200040002100000820100020003000000412000010001800000209000008000c0000010480000400060000008201000200000c0000410080010000840000208040008000c0000010480000400060000008240000200030000004120000100018000002080400080000300001040200040002100000820100020003000000412000010001800000209000008000c000001048000040006
def BB72_Z : BitVec (36 * 72) := 0x6000200001208000003000100000904000001800080000482000000c0004000804100000840002000402080000c0000100020104000001800080000482000000c0004000024100000060002000012080000030001000201040000210000800100820000300000400080410000006000200001208000003000100000904000001800080000482000000c0004000804100000840002000402080000c0000100020104080001800000000482040000c0000000024102000060000000012081000030000000201040800210000000100820400300000000080410200006008000001200100003004000000900080001802000000480040000c0100000804002000840080000402001000c0004000020100080001882000000400040000c410000002000200006208000001000100003104000020000080021082000010000040030041000008
def BB72_X_ker : BitVec (42 * 72) := 0x8000000860020801c14000000430010408e02000000c20030406f81000000880c103bf040800000440c20049c20400000cb0030806e00200000ce0430bd6c101000008e0410fcf010080000470820e79d90040000c00400338040020000890420bbe2300100004e04203f9c100080000d0410bdf6500040000c04103cf020002000060820279c1000100003041033ce000008000b04107bee000004000f0410fffd90000200810400b306100001004a04303b6c00000080cc0410bff2100000408f0400fd3d100000204d0430bc7210000010c50820a79210000008c90c20bba210000004870c00841e10000002490030006000000001c70020c099100000002a0c307bef00000000150c308412100000000088003900000000000044003c000000000000280027000000000000140033000000000000022000e40000000000011000f0000000000000a0009c0000000000005000cc000000000000088003900000000000044003c000000000000280027000000000000140033
def BB72_Z_ker : BitVec (42 * 72) := 0x80000004e0000c2524400000082000863b61200000041000c31db010000008800061a44608000004400030da03040000087000184cd202000008c0000013450100000460000209a2008000086000032d2200400004300001969100200008900000e1f60010000490000073b60008000cb0000032d30004000cd000003bf70002000ce000003f650001000c20000036410000800c40000032d30000400c700000309a0000200810008229f000001004d0004117b500000808e00020a16400000404700010589200000208b0000806d70000010480000400060000008850000229f300000044f00001179400000028f00000a15400000014a0000053e700000002d000000b6d00000001b0000006db000000000800104904000000000400082482000000000200041241000000000100820920000000000080410490000000000040208248000000000020824804000000000010412402000000000008209201000000000004124120000000000002092090000000000001049048
def BB72indrowsx : Fin 30 → Fin 36 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 30, 31]
lemma BB72StrictMono_indrowsx : StrictMono BB72indrowsx := by decide
def BB72indrowsz : Fin 30 → Fin 36 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 30, 31]
lemma BB72StrictMono_indrowsz : StrictMono BB72indrowsz := by decide
def BB72_X_submat : BitVec (30 * 72) := 0x40000008230000200020000004118000100020100000803000020012000000401800010009000000200c0000800480000010060000408201000000000c0020410080000000840010208040000000c0000810480000000060000408240000000030000204120000000018000102080400080000300001040200040002100000820100020003000000412000010001800000209000008000c0000010480000400060000008201000200000c0000410080010000840000208040008000c0000010480000400060000008240000200030000004120000100018000002080400080000300001040200040002100000820100020003000000412000010001800000209000008000c000001048000040006
set_option exponentiation.threshold 10000 in
lemma BB72_X_submat_correct : BB72_X_submat = flatten_matrix (BB72_X_mat.submatrix BB72indrowsx id) := by decide
def BB72_Z_submat : BitVec (30 * 72) := 0x840002000402080000c000010002010400000060002000012080000030001000201040000210000800100820000300000400080410000006000200001208000003000100000904000001800080000482000000c0004000804100000840002000402080000c0000100020104080001800000000482040000c0000000024102000060000000012081000030000000201040800210000000100820400300000000080410200006008000001200100003004000000900080001802000000480040000c0100000804002000840080000402001000c0004000020100080001882000000400040000c410000002000200006208000001000100003104000020000080021082000010000040030041000008
set_option exponentiation.threshold 10000 in
lemma BB72_Z_submat_correct : BB72_Z_submat = flatten_matrix (BB72_Z_mat.submatrix BB72indrowsz id) := by decide
def BB72_X_ker_mat := BitVecMatrix BB72_X_ker
def BB72_Z_ker_mat := BitVecMatrix BB72_Z_ker
lemma BB72_X_ker_mat_correct : flatten_matrix BB72_X_ker_mat = BB72_X_ker := flatten_BitVecMatrix_id _
lemma BB72_Z_ker_mat_correct : flatten_matrix BB72_Z_ker_mat = BB72_Z_ker := flatten_BitVecMatrix_id _
set_option exponentiation.threshold 10000 in
lemma BB72_X_correct : BB72_X = flatten_matrix BB72_X_mat := by decide
set_option exponentiation.threshold 10000 in
lemma BB72_Z_correct : BB72_Z = flatten_matrix BB72_Z_mat := by decide
set_option maxHeartbeats 0 in
lemma BB72_X_rank : 30 ≤ BB72_X_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ BB72indrowsx BB72StrictMono_indrowsx
  rw [linear_indep_SAT_correct,  ←BB72_X_submat_correct, BB72_X_submat]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide (timeout := 9999) (maxSteps := 9999999)
set_option maxHeartbeats 0 in
lemma BB72_Z_rank : 30 ≤ BB72_Z_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ BB72indrowsz BB72StrictMono_indrowsx
  rw [linear_indep_SAT_correct,  ←BB72_Z_submat_correct, BB72_Z_submat]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide (timeout := 9999) (maxSteps := 9999999)
set_option maxHeartbeats 0 in
lemma BB72_X_ker_rank : 42 ≤ BB72_X_ker_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)
  rw [Matrix.submatrix_id_id]
  rw [linear_indep_SAT_correct, BB72_X_ker_mat_correct, BB72_X_ker]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide (timeout := 9999) (maxSteps := 9999999)
set_option maxHeartbeats 0 in
lemma BB72_Z_ker_rank : 42 ≤ BB72_Z_ker_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)
  rw [Matrix.submatrix_id_id]
  rw [linear_indep_SAT_correct, BB72_Z_ker_mat_correct, BB72_Z_ker]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide (timeout := 9999) (maxSteps := 9999999)
set_option exponentiation.threshold 10000
set_option maxHeartbeats 0
lemma BB72_XZ_orth : BB72_X_mat.mutually_orth_rows BB72_Z_mat := by
  rw [←mutually_orth_nat_correct, ←BB72_X_correct, ←BB72_Z_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option exponentiation.threshold 10000
set_option maxHeartbeats 0
lemma BB72_X_ker_orth : BB72_X_mat.mutually_orth_rows BB72_X_ker_mat := by
  rw [←mutually_orth_nat_correct, ←BB72_X_correct, BB72_X_ker_mat_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option exponentiation.threshold 10000
set_option maxHeartbeats 0
lemma BB72_Z_ker_orth : BB72_Z_mat.mutually_orth_rows BB72_Z_ker_mat := by
  rw [←mutually_orth_nat_correct, ←BB72_Z_correct, BB72_Z_ker_mat_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option maxHeartbeats 0 in
lemma BB72_dist_z : lt_dist_sat BB72_X BB72_Z_ker 5 7 := by
  rw [BB72_X, BB72_Z_ker]
  simp (maxSteps := 9999999) only [lt_dist_sat, Nat.reduceMul, loc_constraints, loc_constraints_aux, loc_constraints_ith,
  symmetry_constraints, symmetry_constraints_aux,  Nat.add_one_sub_one, Nat.lt_add_one, getElem!_pos, loc_constraints_ith_jth_aux,
  loc_constraints_ith_jth, one_mul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff,
  Nat.reduceLT, Nat.one_lt_ofNat, Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, dot_product_aux, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  bv_decide (timeout := 9999) (maxSteps := 9999999)
set_option maxHeartbeats 0 in
lemma BB72_dist_x : lt_dist_sat BB72_Z BB72_X_ker 5 7 := by
  rw [BB72_Z, BB72_X_ker]
  simp (maxSteps := 9999999) only [lt_dist_sat, Nat.reduceMul, loc_constraints, loc_constraints_aux, loc_constraints_ith,
  symmetry_constraints, symmetry_constraints_aux,  Nat.add_one_sub_one, Nat.lt_add_one, getElem!_pos, loc_constraints_ith_jth_aux,
  loc_constraints_ith_jth, one_mul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff,
  Nat.reduceLT, Nat.one_lt_ofNat, Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, dot_product_aux, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  bv_decide (timeout := 9999) (maxSteps := 9999999)
lemma BB72_X_ker_is_ker : BB72_X_ker_mat.is_ker_for BB72_X_mat := by
  apply Matrix.is_ker_for_of_rank_sum_mutually_orth _ _ BB72_X_rank BB72_X_ker_rank (by norm_num) BB72_X_ker_orth
lemma BB72_Z_ker_is_ker : BB72_Z_ker_mat.is_ker_for BB72_Z_mat := by
  apply Matrix.is_ker_for_of_rank_sum_mutually_orth _ _ BB72_Z_rank BB72_Z_ker_rank (by norm_num) BB72_Z_ker_orth
def BB72_css : CSS_pair 72 36 36 :=
  CSS_pair.of_matrices BB72_X_mat BB72_Z_mat BB72_XZ_orth
theorem BB72_dist_6 : 6 ≤ BB72_css.toBSM.distance (by norm_num) := by
  apply bitvec_sat_translation_correct BB72_css
      BB72_Z_ker_mat BB72_Z_ker_is_ker
      BB72_X_ker_mat BB72_X_ker_is_ker (by norm_num) _ _
  · rw [BB72_css, CSS_pair.of_matrices, ←BB72_X_correct, BB72_Z_ker_mat_correct]
    exact BB72_dist_z
  rw [BB72_css, CSS_pair.of_matrices, ←BB72_Z_correct, BB72_X_ker_mat_correct]
  exact BB72_dist_x

#print axioms BB72_dist_6
