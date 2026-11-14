import LeanQEC.ComputerAlgebra.BitVecSAT
import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide
import LeanQEC.ComputerAlgebra.BitVecCorrectness
import LeanQEC.Stabilizer.BB
import LeanQEC.Stabilizer.BitVecSATToDist
set_option maxRecDepth 9999999
def GB54_A :=
  let l := 27
  let m := 1
  BB4_matrix l m (true, 8) (true, 13) (true, 15) (true, 16)
def GB54_B :=
  let l := 27
  let m := 1
  BB4_matrix l m (true, 7) (true, 8) (true, 10) (true, 15)
def GB54_X_mat := GB54_A.hstack_fin GB54_B
def GB54_Z_mat := GB54_B.transpose.hstack_fin GB54_A.transpose
def GB54_X : BitVec (27 * 54) := 0x2160000d08000042c0001a100000858000342000010b000068400002160000d08000042c0001a100000858000342800010a000068700002140000d0600004280001a2c00008100003458000102000068b00002040000d160000508000182c0000a100003858000142000050b000068400002160000d08000042c0001a100000858000342000010b000068400002160000d08000042c0001a100000858000342000010b000068400002160000d08000042c0001a100
def GB54_Z : BitVec (27 * 54) := 0x2160000d08000042c0001a100000858000342000010b000068400002160000d08000042c0001a100000858000342000010b000068400002160000d08000042c0001a100000858000342800010a000068700002140000d0600004280001a2c00008100003458000102000068b00002040000d160000508000182c0000a100003858000142000050b000068400002160000d08000042c0001a100000858000342000010b000068400002160000d08000042c0001a1000
def GB54_X_ker : BitVec (28 * 54) := 0x8000000f6ae87d000000212a2f0200000042545e0400000084a8bc080000010951781000000212a2f0200000fbdaba00400001f7b57400800003ef6ae801000007ded5d0020000f04254400400021f7b570008000bc10950001000178212a00020002f042540004003a1f7b500008008bc10940001002e87ded0000200a2f04240000402ba1f7b0000080a8bc10800001015178210000020d5d0fbc0000042545e0800000084a8bc100000010951782000000212a2f040000007ffffff
def GB54_Z_ker : BitVec (28 * 54) := 0x8000000f6ae87d000000212a2f0200000042545e0400000084a8bc080000010951781000000212a2f0200000fbdaba00400001f7b57400800003ef6ae801000007ded5d0020000f04254400400021f7b570008000bc10950001000178212a00020002f042540004003a1f7b500008008bc10940001002e87ded0000200a2f04240000402ba1f7b0000080a8bc10800001015178210000020d5d0fbc0000042545e0800000084a8bc100000010951782000000212a2f040000007ffffff
def GB54indrowsx : Fin 26 → Fin 27 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
lemma GB54StrictMono_indrowsx : StrictMono GB54indrowsx := by decide
def GB54indrowsz : Fin 26 → Fin 27 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
lemma GB54StrictMono_indrowsz : StrictMono GB54indrowsz := by decide
def GB54_X_submat : BitVec (26 * 54) := 0x42c0001a100000858000342000010b000068400002160000d08000042c0001a100000858000342800010a000068700002140000d0600004280001a2c00008100003458000102000068b00002040000d160000508000182c0000a100003858000142000050b000068400002160000d08000042c0001a100000858000342000010b000068400002160000d08000042c0001a100000858000342000010b000068400002160000d08000042c0001a100
set_option exponentiation.threshold 10000 in
lemma GB54_X_submat_correct : GB54_X_submat = flatten_matrix (GB54_X_mat.submatrix GB54indrowsx id) := by decide
def GB54_Z_submat : BitVec (26 * 54) := 0x42c0001a100000858000342000010b000068400002160000d08000042c0001a100000858000342000010b000068400002160000d08000042c0001a100000858000342800010a000068700002140000d0600004280001a2c00008100003458000102000068b00002040000d160000508000182c0000a100003858000142000050b000068400002160000d08000042c0001a100000858000342000010b000068400002160000d08000042c0001a1000
set_option exponentiation.threshold 10000 in
lemma GB54_Z_submat_correct : GB54_Z_submat = flatten_matrix (GB54_Z_mat.submatrix GB54indrowsz id) := by decide
def GB54_X_ker_mat := BitVecMatrix GB54_X_ker
def GB54_Z_ker_mat := BitVecMatrix GB54_Z_ker
lemma GB54_X_ker_mat_correct : flatten_matrix GB54_X_ker_mat = GB54_X_ker := flatten_BitVecMatrix_id _
lemma GB54_Z_ker_mat_correct : flatten_matrix GB54_Z_ker_mat = GB54_Z_ker := flatten_BitVecMatrix_id _
set_option exponentiation.threshold 10000 in
lemma GB54_X_correct : GB54_X = flatten_matrix GB54_X_mat := by decide
set_option exponentiation.threshold 10000 in
lemma GB54_Z_correct : GB54_Z = flatten_matrix GB54_Z_mat := by decide
set_option maxHeartbeats 0 in
lemma GB54_X_rank : 26 ≤ GB54_X_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ GB54indrowsx GB54StrictMono_indrowsx
  rw [linear_indep_SAT_correct,  ←GB54_X_submat_correct, GB54_X_submat]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide (timeout := 9999) (maxSteps := 9999999)
set_option maxHeartbeats 0 in
lemma GB54_Z_rank : 26 ≤ GB54_Z_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ GB54indrowsz GB54StrictMono_indrowsx
  rw [linear_indep_SAT_correct,  ←GB54_Z_submat_correct, GB54_Z_submat]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide (timeout := 9999) (maxSteps := 9999999)
set_option maxHeartbeats 0 in
lemma GB54_X_ker_rank : 28 ≤ GB54_X_ker_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)
  rw [Matrix.submatrix_id_id]
  rw [linear_indep_SAT_correct, GB54_X_ker_mat_correct, GB54_X_ker]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide (timeout := 9999) (maxSteps := 9999999)
set_option maxHeartbeats 0 in
lemma GB54_Z_ker_rank : 28 ≤ GB54_Z_ker_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)
  rw [Matrix.submatrix_id_id]
  rw [linear_indep_SAT_correct, GB54_Z_ker_mat_correct, GB54_Z_ker]
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
lemma GB54_XZ_orth : GB54_X_mat.mutually_orth_rows GB54_Z_mat := by
  rw [←mutually_orth_nat_correct, ←GB54_X_correct, ←GB54_Z_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option exponentiation.threshold 10000
set_option maxHeartbeats 0
lemma GB54_X_ker_orth : GB54_X_mat.mutually_orth_rows GB54_X_ker_mat := by
  rw [←mutually_orth_nat_correct, ←GB54_X_correct, GB54_X_ker_mat_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option exponentiation.threshold 10000
set_option maxHeartbeats 0
lemma GB54_Z_ker_orth : GB54_Z_mat.mutually_orth_rows GB54_Z_ker_mat := by
  rw [←mutually_orth_nat_correct, ←GB54_Z_correct, GB54_Z_ker_mat_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option maxHeartbeats 0 in
lemma GB54_dist_z : lt_dist_sat GB54_X GB54_Z_ker 9 6 := by
  rw [GB54_X, GB54_Z_ker]
  simp (maxSteps := 9999999) only [lt_dist_sat, Nat.reduceMul, loc_constraints, loc_constraints_aux, loc_constraints_ith,
  symmetry_constraints, symmetry_constraints_aux,  Nat.add_one_sub_one, Nat.lt_add_one, getElem!_pos, loc_constraints_ith_jth_aux,
  loc_constraints_ith_jth, one_mul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff,
  Nat.reduceLT, Nat.one_lt_ofNat, Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, dot_product_aux, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  bv_decide (timeout := 9999) (maxSteps := 9999999)
set_option maxHeartbeats 0 in
lemma GB54_dist_x : lt_dist_sat GB54_Z GB54_X_ker 9 6 := by
  rw [GB54_Z, GB54_X_ker]
  simp (maxSteps := 9999999) only [lt_dist_sat, Nat.reduceMul, loc_constraints, loc_constraints_aux, loc_constraints_ith,
  symmetry_constraints, symmetry_constraints_aux,  Nat.add_one_sub_one, Nat.lt_add_one, getElem!_pos, loc_constraints_ith_jth_aux,
  loc_constraints_ith_jth, one_mul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff,
  Nat.reduceLT, Nat.one_lt_ofNat, Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, dot_product_aux, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  bv_decide (timeout := 9999) (maxSteps := 9999999)
lemma GB54_X_ker_is_ker : GB54_X_ker_mat.is_ker_for GB54_X_mat := by
  apply Matrix.is_ker_for_of_rank_sum_mutually_orth _ _ GB54_X_rank GB54_X_ker_rank (by norm_num) GB54_X_ker_orth
lemma GB54_Z_ker_is_ker : GB54_Z_ker_mat.is_ker_for GB54_Z_mat := by
  apply Matrix.is_ker_for_of_rank_sum_mutually_orth _ _ GB54_Z_rank GB54_Z_ker_rank (by norm_num) GB54_Z_ker_orth
def GB54_css : CSS_pair 54 27 27 :=
  CSS_pair.of_matrices GB54_X_mat GB54_Z_mat GB54_XZ_orth
theorem GB54_dist_10 : 10 ≤ GB54_css.toBSM.distance (by norm_num) := by
  apply bitvec_sat_translation_correct GB54_css
      GB54_Z_ker_mat GB54_Z_ker_is_ker
      GB54_X_ker_mat GB54_X_ker_is_ker (by norm_num) _ _
  · rw [GB54_css, CSS_pair.of_matrices, ←GB54_X_correct, GB54_Z_ker_mat_correct]
    exact GB54_dist_z
  rw [GB54_css, CSS_pair.of_matrices, ←GB54_Z_correct, GB54_X_ker_mat_correct]
  exact GB54_dist_x
