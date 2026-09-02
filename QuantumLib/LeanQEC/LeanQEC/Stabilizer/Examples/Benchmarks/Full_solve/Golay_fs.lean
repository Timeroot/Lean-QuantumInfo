import LeanQEC.ComputerAlgebra.BitVecSAT
import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide
import LeanQEC.ComputerAlgebra.BitVecCorrectness
import LeanQEC.Stabilizer.BitVecSATToDist

set_option maxRecDepth 9999999

def golay_mat : BitVec (11 * 23) :=
  0x7c94010b78042de010b78042de0104ea840c8f100c764031d9003e4c00f92

def golay_ker : BitVec (12 * 23) :=
0x800ae2801f248034a88063b080cd8080cd8080cd8085bc0085bc0085bc00ae3000ae3

def golay_mat' : Matrix (Fin 11) (Fin 23) (ZMod 2) :=
  !![0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def golay_ker' : Matrix (Fin 12) (Fin 23) (ZMod 2) :=
  !![1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

lemma golay_mat_correct : golay_mat = flatten_matrix golay_mat' := by decide

set_option exponentiation.threshold 276
lemma golay_ker_correct : golay_ker = flatten_matrix golay_ker' := by decide


lemma golay_ind : LinearIndependent (ZMod 2) golay_mat' := by
  rw [linear_indep_SAT_correct, ←golay_mat_correct, golay_mat]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
    getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
    Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
    BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
    Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
    bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide (timeout := 9999)

lemma golay_ker_ind : LinearIndependent (ZMod 2) golay_ker' := by
  rw [linear_indep_SAT_correct, ←golay_ker_correct, golay_ker]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
    getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
    Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
    BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
    Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
    bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide (timeout := 9999)

lemma golay_mat_rank : 11 ≤ golay_mat'.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)
  rw [Matrix.submatrix_id_id]
  apply golay_ind

lemma golay_ker_rank : 12 ≤ golay_ker'.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)
  rw [Matrix.submatrix_id_id]
  apply golay_ker_ind




lemma golay_orth : golay_mat'.mutually_orth_rows golay_mat' := by
  rw [←mutually_orth_nat_correct, ←golay_mat_correct, golay_mat]
  simp [bitvec_mutually_orth_nat]
  native_decide

lemma golay_mat_ker_orth : golay_mat'.mutually_orth_rows golay_ker' := by
  rw [←mutually_orth_nat_correct, ←golay_mat_correct, ←golay_ker_correct, golay_mat, golay_ker]
  simp [bitvec_mutually_orth_nat]
  native_decide



set_option maxHeartbeats 0 in
lemma golay_dist : lt_dist_sat (flatten_matrix golay_mat') (flatten_matrix golay_ker') 6 5
  := by
  rw [←golay_mat_correct, ←golay_ker_correct, golay_mat, golay_ker]
  simp only [lt_dist_sat, Nat.reduceMul, loc_constraints, loc_constraints_aux, loc_constraints_ith,
    Nat.add_one_sub_one, Nat.lt_add_one, getElem!_pos, loc_constraints_ith_jth_aux,
    loc_constraints_ith_jth, one_mul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff,
    Nat.reduceLT, Nat.one_lt_ofNat, Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parity_constraints,
    parity_constraints_aux, BitVec.dot_product, dot_product_aux, BitVec.row,
    Bool.not_eq_eq_eq_not, Bool.not_true,
    bne_eq_false_iff_eq, decide_eq_true_eq, rowspace_constraints,
    rowspace_constraints_aux, not_and, and_imp]
  bv_decide (timeout := 9999)

lemma golay_ker_mat_correct : golay_ker'.is_ker_for golay_mat' := by
  apply Matrix.is_ker_for_of_rank_sum_mutually_orth _ _ golay_mat_rank golay_ker_rank (by norm_num) golay_mat_ker_orth

def golay_css : CSS_pair 23 11 11 := CSS_pair.of_matrices golay_mat' golay_mat' golay_orth

theorem golay_dist_3 : 7 ≤ golay_css.toBSM.distance (by norm_num) := by
  apply bitvec_sat_translation_correct golay_css golay_ker' golay_ker_mat_correct golay_ker' golay_ker_mat_correct (by norm_num) _ _
  all_goals rw [golay_css, CSS_pair.of_matrices]
  all_goals exact golay_dist
