import LeanQEC.ComputerAlgebra.BitVecSAT
import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide
import LeanQEC.ComputerAlgebra.BitVecCorrectness
import LeanQEC.Stabilizer.BB
import LeanQEC.Stabilizer.BitVecSATToDist
import LeanQEC.timedbv

set_option maxRecDepth 9999999
def BB18_A :=
  let l := 3
  let m := 3
  BB3_matrix l m (true, 0) (true, 1) (false, 1)
def BB18_B :=
  let l := 3
  let m := 3
  BB3_matrix l m (true, 0) (true, 2) (false, 2)
def BB18_X_mat := BB18_A.hstack_fin BB18_B
def BB18_Z_mat := BB18_B.transpose.hstack_fin BB18_A.transpose
def BB18_X : BitVec (9 * 18) := 0x341446860a90c11a4a034b0149620c25418588a0b
def BB18_Z : BitVec (9 * 18) := 0x341446860a90c11a4a034b0149620c25418588a0b
def BB18_X_ker : BitVec (11 * 18) := 0x2003d400f8803b100d0201a040a40875011b40245005cc00ee
def BB18_Z_ker : BitVec (11 * 18) := 0x2003d400f8803b100d0201a040a40875011b40245005cc00ee
def BB18indrowsx : Fin 7 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6]
lemma BB18StrictMono_indrowsx : StrictMono BB18indrowsx := by decide
def BB18indrowsz : Fin 7 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6]
lemma BB18StrictMono_indrowsz : StrictMono BB18indrowsz := by decide
def BB18_X_submat : BitVec (7 * 18) := 0x290c11a4a034b0149620c25418588a0b
set_option exponentiation.threshold 10000 in
lemma BB18_X_submat_correct : BB18_X_submat = flatten_matrix (BB18_X_mat.submatrix BB18indrowsx id) := by decide
def BB18_Z_submat : BitVec (7 * 18) := 0x290c11a4a034b0149620c25418588a0b
set_option exponentiation.threshold 10000 in
lemma BB18_Z_submat_correct : BB18_Z_submat = flatten_matrix (BB18_Z_mat.submatrix BB18indrowsz id) := by decide
def BB18_X_ker_mat := BitVecMatrix BB18_X_ker
def BB18_Z_ker_mat := BitVecMatrix BB18_Z_ker
lemma BB18_X_ker_mat_correct : flatten_matrix BB18_X_ker_mat = BB18_X_ker := flatten_BitVecMatrix_id _
lemma BB18_Z_ker_mat_correct : flatten_matrix BB18_Z_ker_mat = BB18_Z_ker := flatten_BitVecMatrix_id _
set_option exponentiation.threshold 10000 in
lemma BB18_X_correct : BB18_X = flatten_matrix BB18_X_mat := by decide
set_option exponentiation.threshold 10000 in
lemma BB18_Z_correct : BB18_Z = flatten_matrix BB18_Z_mat := by decide
set_option maxHeartbeats 0 in
lemma BB18_X_rank : 7 ≤ BB18_X_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ BB18indrowsx BB18StrictMono_indrowsx
  rw [linear_indep_SAT_correct,  ←BB18_X_submat_correct, BB18_X_submat]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide (timeout := 9999)
set_option maxHeartbeats 0 in
lemma BB18_Z_rank : 7 ≤ BB18_Z_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ BB18indrowsz BB18StrictMono_indrowsx
  rw [linear_indep_SAT_correct,  ←BB18_Z_submat_correct, BB18_Z_submat]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide (timeout := 9999)
set_option maxHeartbeats 0 in
lemma BB18_X_ker_rank : 11 ≤ BB18_X_ker_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)
  rw [Matrix.submatrix_id_id]
  rw [linear_indep_SAT_correct, BB18_X_ker_mat_correct, BB18_X_ker]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide (timeout := 9999)
set_option maxHeartbeats 0 in
lemma BB18_Z_ker_rank : 11 ≤ BB18_Z_ker_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)
  rw [Matrix.submatrix_id_id]
  rw [linear_indep_SAT_correct, BB18_Z_ker_mat_correct, BB18_Z_ker]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide (timeout := 9999)
set_option exponentiation.threshold 10000
set_option maxHeartbeats 0
lemma BB18_XZ_orth : BB18_X_mat.mutually_orth_rows BB18_Z_mat := by
  rw [←mutually_orth_nat_correct, ←BB18_X_correct, ←BB18_Z_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option exponentiation.threshold 10000
set_option maxHeartbeats 0
lemma BB18_X_ker_orth : BB18_X_mat.mutually_orth_rows BB18_X_ker_mat := by
  rw [←mutually_orth_nat_correct, ←BB18_X_correct, BB18_X_ker_mat_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option exponentiation.threshold 10000
set_option maxHeartbeats 0
lemma BB18_Z_ker_orth : BB18_Z_mat.mutually_orth_rows BB18_Z_ker_mat := by
  rw [←mutually_orth_nat_correct, ←BB18_Z_correct, BB18_Z_ker_mat_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option maxHeartbeats 0 in
lemma BB18_dist_z : lt_dist_sat BB18_X BB18_Z_ker 3 5 := by
  rw [BB18_X, BB18_Z_ker]
  simp (maxSteps := 9999999) only [lt_dist_sat, Nat.reduceMul, loc_constraints, loc_constraints_aux, loc_constraints_ith,
  symmetry_constraints, symmetry_constraints_aux,  Nat.add_one_sub_one, Nat.lt_add_one, getElem!_pos, loc_constraints_ith_jth_aux,
  loc_constraints_ith_jth, one_mul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff,
  Nat.reduceLT, Nat.one_lt_ofNat, Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, dot_product_aux, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  bv_decide (timeout := 9999) (maxSteps := 9999999)
set_option maxHeartbeats 0 in
lemma BB18_dist_x : lt_dist_sat BB18_Z BB18_X_ker 3 5 := by
  rw [BB18_Z, BB18_X_ker]
  simp (maxSteps := 9999999) only [lt_dist_sat, Nat.reduceMul, loc_constraints, loc_constraints_aux, loc_constraints_ith,
  symmetry_constraints, symmetry_constraints_aux,  Nat.add_one_sub_one, Nat.lt_add_one, getElem!_pos, loc_constraints_ith_jth_aux,
  loc_constraints_ith_jth, one_mul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff,
  Nat.reduceLT, Nat.one_lt_ofNat, Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, dot_product_aux, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  bv_decide (timeout := 9999) (maxSteps := 9999999)
lemma BB18_X_ker_is_ker : BB18_X_ker_mat.is_ker_for BB18_X_mat := by
  apply Matrix.is_ker_for_of_rank_sum_mutually_orth _ _ BB18_X_rank BB18_X_ker_rank (by norm_num) BB18_X_ker_orth
lemma BB18_Z_ker_is_ker : BB18_Z_ker_mat.is_ker_for BB18_Z_mat := by
  apply Matrix.is_ker_for_of_rank_sum_mutually_orth _ _ BB18_Z_rank BB18_Z_ker_rank (by norm_num) BB18_Z_ker_orth
def BB18_css : CSS_pair 18 9 9 :=
  CSS_pair.of_matrices BB18_X_mat BB18_Z_mat BB18_XZ_orth
theorem BB18_dist_4 : 4 ≤ BB18_css.toBSM.distance (by norm_num) := by
  apply bitvec_sat_translation_correct BB18_css
      BB18_Z_ker_mat BB18_Z_ker_is_ker
      BB18_X_ker_mat BB18_X_ker_is_ker (by norm_num) _ _
  · rw [BB18_css, CSS_pair.of_matrices, ←BB18_X_correct, BB18_Z_ker_mat_correct]
    exact BB18_dist_z
  rw [BB18_css, CSS_pair.of_matrices, ←BB18_Z_correct, BB18_X_ker_mat_correct]
  exact BB18_dist_x
