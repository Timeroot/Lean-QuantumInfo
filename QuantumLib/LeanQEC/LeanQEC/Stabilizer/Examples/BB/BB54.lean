import LeanQEC.ComputerAlgebra.BitVecSAT
import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide
import LeanQEC.ComputerAlgebra.BitVecCorrectness
import LeanQEC.Stabilizer.BB
import LeanQEC.Stabilizer.BitVecSATToDist
--for SAT query logging:
--set_option sat.solver "./logger.bat"
set_option maxRecDepth 9999999
def BB54_A :=
  let l := 3
  let m := 9
  BB3_matrix l m (true, 0) (false, 2) (false, 4)
def BB54_B :=
  let l := 3
  let m := 9
  BB3_matrix l m (true, 1) (true, 2) (false, 3)
def BB54_X_mat := BB54_A.hstack_fin BB54_B
def BB54_Z_mat := BB54_B.transpose.hstack_fin BB54_A.transpose
def BB54_X : BitVec (27 * 54) := 0x9008042800000120100850000002402050800008008040a10000100100854000002002010a800000400402150000008008042a000001001008540000800120000850010002400010a00200048000a10004100100014200082002000a800010400400150000208008002a00004100100054000082002000a802010002000010a402000400002148040008000142100820000002842010400000150040208000002a00804100000054010082000000a80201040000015
def BB54_Z : BitVec (27 * 54) := 0x2a00000082010054000001040200a800000208040150000004100802a00000082010850000001040210a00004000804a100000800100942000010002010054001001040000a800200208000150004004100002a00080082000054001001040010a000200208002140004800100142000090002002840001200040000a840200200000150804004000002a10080080000054201001000000a8402002000021408040040000428100900000028402012000000508040240
def BB54_X_ker : BitVec (31 * 54) := 0x20000019e8a47940000046f3d800800000968a00010000067f3d144200001000de140400002002d028080001948fe5401000047b001ec02000094000500040006523d1e40080011ecde000010002502d0000020019e8fe5100040046f00050000800968000a00010067f29150000201000f67b00004020028140000081948a45100001047b3d850000020940a00a00000467a3d1500000091bcde7b00000125a2d1400000039fcfe7900000016d0000000000036c0000000000000b6800000000001b600000000000005b400000000000db
def BB54_Z_ker : BitVec (31 * 54) := 0x20001008cc288640004023d16d008001008e82a8710004021d049002001008a80e07040040215000000801008b84f03010040217082080201008bc5f4200404003b0e710008100008240200104003a0af14002100098650200044002802d140009000bc7542000140008009040003000fc71c000002023b1df8c000040808041200000823a1d7a80000108984d16000002228145a00000048bc5f57000000a08041200000018fc7fc7000000124004900000002480092000000049001240000000024924000000000492480000000009249
def BB54indrowsx : Fin 23 → Fin 27 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19, 20, 21, 22, 23, 24]
lemma BB54StrictMono_indrowsx : StrictMono BB54indrowsx := by decide
def BB54indrowsz : Fin 23 → Fin 27 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19, 20, 21, 22, 23, 24]
lemma BB54StrictMono_indrowsz : StrictMono BB54indrowsz := by decide
def BB54_X_submat : BitVec (23 * 54) := 0x2402050800008008040a10000100100854000002002010a800000400402150000008008042a000001001008540000200048000a10004100100014200082002000a800010400400150000208008002a00004100100054000082002000a802010002000010a402000400002148040008000142100820000002842010400000150040208000002a00804100000054010082000000a80201040000015
set_option exponentiation.threshold 10000 in
lemma BB54_X_submat_correct : BB54_X_submat = flatten_matrix (BB54_X_mat.submatrix BB54indrowsx id) := by decide
def BB54_Z_submat : BitVec (23 * 54) := 0xa800000208040150000004100802a00000082010850000001040210a00004000804a1000008001009420000100020100150004004100002a00080082000054001001040010a000200208002140004800100142000090002002840001200040000a840200200000150804004000002a10080080000054201001000000a8402002000021408040040000428100900000028402012000000508040240
set_option exponentiation.threshold 10000 in
lemma BB54_Z_submat_correct : BB54_Z_submat = flatten_matrix (BB54_Z_mat.submatrix BB54indrowsz id) := by decide
def BB54_X_ker_mat := BitVecMatrix BB54_X_ker
def BB54_Z_ker_mat := BitVecMatrix BB54_Z_ker
lemma BB54_X_ker_mat_correct : flatten_matrix BB54_X_ker_mat = BB54_X_ker := flatten_BitVecMatrix_id _
lemma BB54_Z_ker_mat_correct : flatten_matrix BB54_Z_ker_mat = BB54_Z_ker := flatten_BitVecMatrix_id _
set_option exponentiation.threshold 10000 in
lemma BB54_X_correct : BB54_X = flatten_matrix BB54_X_mat := by decide
set_option exponentiation.threshold 10000 in
lemma BB54_Z_correct : BB54_Z = flatten_matrix BB54_Z_mat := by decide
set_option maxHeartbeats 0 in
lemma BB54_X_rank : 23 ≤ BB54_X_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ BB54indrowsx BB54StrictMono_indrowsx
  rw [linear_indep_SAT_correct,  ←BB54_X_submat_correct, BB54_X_submat]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_check "BB54.lean-BB54_X_rank-53-2.lrat"
set_option maxHeartbeats 0 in
lemma BB54_Z_rank : 23 ≤ BB54_Z_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ BB54indrowsz BB54StrictMono_indrowsx
  rw [linear_indep_SAT_correct,  ←BB54_Z_submat_correct, BB54_Z_submat]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_check "BB54.lean-BB54_Z_rank-65-2.lrat"
set_option maxHeartbeats 0 in
lemma BB54_X_ker_rank : 31 ≤ BB54_X_ker_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)
  rw [Matrix.submatrix_id_id]
  rw [linear_indep_SAT_correct, BB54_X_ker_mat_correct, BB54_X_ker]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_normalize
set_option maxHeartbeats 0 in
lemma BB54_Z_ker_rank : 31 ≤ BB54_Z_ker_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)
  rw [Matrix.submatrix_id_id]
  rw [linear_indep_SAT_correct, BB54_Z_ker_mat_correct, BB54_Z_ker]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_normalize
set_option exponentiation.threshold 10000
set_option maxHeartbeats 0
lemma BB54_XZ_orth : BB54_X_mat.mutually_orth_rows BB54_Z_mat := by
  rw [←mutually_orth_nat_correct, ←BB54_X_correct, ←BB54_Z_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option exponentiation.threshold 10000
set_option maxHeartbeats 0
lemma BB54_X_ker_orth : BB54_X_mat.mutually_orth_rows BB54_X_ker_mat := by
  rw [←mutually_orth_nat_correct, ←BB54_X_correct, BB54_X_ker_mat_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option exponentiation.threshold 10000
set_option maxHeartbeats 0
lemma BB54_Z_ker_orth : BB54_Z_mat.mutually_orth_rows BB54_Z_ker_mat := by
  rw [←mutually_orth_nat_correct, ←BB54_Z_correct, BB54_Z_ker_mat_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option maxHeartbeats 0 in
lemma BB54_dist_z : lt_dist_sat BB54_X BB54_Z_ker 5 6 := by
  rw [BB54_X, BB54_Z_ker]
  simp (maxSteps := 9999999) only [lt_dist_sat, Nat.reduceMul, loc_constraints, loc_constraints_aux, loc_constraints_ith,
  symmetry_constraints, symmetry_constraints_aux,  Nat.add_one_sub_one, Nat.lt_add_one, getElem!_pos, loc_constraints_ith_jth_aux,
  loc_constraints_ith_jth, one_mul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff,
  Nat.reduceLT, Nat.one_lt_ofNat, Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, dot_product_aux, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  bv_check (timeout := 9999) (maxSteps := 9999999) "BB54.lean-BB54_dist_z-120-2.lrat"
set_option maxHeartbeats 0 in
lemma BB54_dist_x : lt_dist_sat BB54_Z BB54_X_ker 5 6 := by
  rw [BB54_Z, BB54_X_ker]
  simp (maxSteps := 9999999) only [lt_dist_sat, Nat.reduceMul, loc_constraints, loc_constraints_aux, loc_constraints_ith,
  symmetry_constraints, symmetry_constraints_aux,  Nat.add_one_sub_one, Nat.lt_add_one, getElem!_pos, loc_constraints_ith_jth_aux,
  loc_constraints_ith_jth, one_mul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff,
  Nat.reduceLT, Nat.one_lt_ofNat, Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, dot_product_aux, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  bv_check (timeout := 9999) (maxSteps := 9999999)"BB54.lean-BB54_dist_x-131-2.lrat"
lemma BB54_X_ker_is_ker : BB54_X_ker_mat.is_ker_for BB54_X_mat := by
  apply Matrix.is_ker_for_of_rank_sum_mutually_orth _ _ BB54_X_rank BB54_X_ker_rank (by norm_num) BB54_X_ker_orth
lemma BB54_Z_ker_is_ker : BB54_Z_ker_mat.is_ker_for BB54_Z_mat := by
  apply Matrix.is_ker_for_of_rank_sum_mutually_orth _ _ BB54_Z_rank BB54_Z_ker_rank (by norm_num) BB54_Z_ker_orth
def BB54_css : CSS_pair 54 27 27 :=
  CSS_pair.of_matrices BB54_X_mat BB54_Z_mat BB54_XZ_orth
theorem BB54_dist_6 : 6 ≤ BB54_css.toBSM.distance (by norm_num) := by
  apply bitvec_sat_translation_correct BB54_css
      BB54_Z_ker_mat BB54_Z_ker_is_ker
      BB54_X_ker_mat BB54_X_ker_is_ker (by norm_num) _ _
  · rw [BB54_css, CSS_pair.of_matrices, ←BB54_X_correct, BB54_Z_ker_mat_correct]
    exact BB54_dist_z
  rw [BB54_css, CSS_pair.of_matrices, ←BB54_Z_correct, BB54_X_ker_mat_correct]
  exact BB54_dist_x
