import LeanQEC.ComputerAlgebra.BitVecSAT
import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide
import LeanQEC.ComputerAlgebra.BitVecCorrectness
import LeanQEC.Stabilizer.BitVecSATToDist


set_option maxRecDepth 9999999
def steane_mat : BitVec (3 * 7) :=
  0x1d2d69

def steane_ker : BitVec (4 * 7) :=
  0x8e94b0b

def steane_mat' : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 1, 0, 1, 1;
    0, 1, 0, 1, 1, 0, 1;
    0, 0, 1, 0, 1, 1, 1]

def steane_ker' : Matrix (Fin 4) (Fin 7) (ZMod 2) :=
 !![1, 1, 0, 1, 0, 0, 0;
 0, 1, 1, 0, 1, 0, 0;
 1, 0, 1, 0, 0, 1, 0;
 1, 1, 1, 0, 0, 0, 1;]


lemma steane_mat_correct : steane_mat = flatten_matrix steane_mat' := by decide
lemma steane_ker_correct : steane_ker = flatten_matrix steane_ker' := by decide

lemma steane_ind : LinearIndependent (ZMod 2) steane_mat' := by
  rw [linear_indep_SAT_correct, ←steane_mat_correct, steane_mat]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
    getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
    Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
    BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
    Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
    bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  sorry

lemma steane_ker_ind : LinearIndependent (ZMod 2) steane_ker' := by
  rw [linear_indep_SAT_correct, ←steane_ker_correct, steane_ker]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
    getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
    Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
    BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
    Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
    bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  sorry

lemma steane_mat_rank : 3 ≤ steane_mat'.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)
  rw [Matrix.submatrix_id_id]
  apply steane_ind

lemma steane_ker_rank : 4 ≤ steane_ker'.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)
  rw [Matrix.submatrix_id_id]
  apply steane_ker_ind




lemma steane_orth : steane_mat'.mutually_orth_rows steane_mat' := by
  rw [←mutually_orth_nat_correct, ←steane_mat_correct]
  unfold bitvec_mutually_orth_nat
  native_decide


lemma steane_mat_ker_orth : steane_mat'.mutually_orth_rows steane_ker' := by
  rw [←mutually_orth_nat_correct, ←steane_mat_correct, ←steane_ker_correct]
  unfold bitvec_mutually_orth_nat
  native_decide





set_option maxHeartbeats 0 in
lemma steane_dist : lt_dist_sat (flatten_matrix steane_mat') (flatten_matrix steane_ker') 2 3
  := by
  rw [←steane_mat_correct, ←steane_ker_correct, steane_mat, steane_ker]
  simp only [lt_dist_sat, symmetry_constraints, symmetry_constraints_aux, Nat.reduceMul, loc_constraints, loc_constraints_aux, loc_constraints_ith,
    Nat.add_one_sub_one, Nat.lt_add_one, getElem!_pos, loc_constraints_ith_jth_aux,
    loc_constraints_ith_jth, one_mul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff,
    Nat.reduceLT, Nat.one_lt_ofNat, Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parity_constraints,
    parity_constraints_aux, BitVec.dot_product, dot_product_aux, BitVec.row,
    Bool.not_eq_eq_eq_not, Bool.not_true,
    bne_eq_false_iff_eq, decide_eq_true_eq, rowspace_constraints,
    rowspace_constraints_aux, not_and, and_imp, BitVec.reduceExtractLsb', BitVec.reduceGetElem, Bool.and_true, Bool.and_false,
    bne_self_eq_false, Bool.bne_false, Bool.false_bne, bne_iff_ne, ne_eq, not_or, Decidable.not_not]
  sorry
lemma steane_ker_mat_correct : steane_ker'.is_ker_for steane_mat' := by
  apply Matrix.is_ker_for_of_rank_sum_mutually_orth _ _ steane_mat_rank steane_ker_rank (by norm_num) steane_mat_ker_orth

def steane_css : CSS_pair 7 3 3 := CSS_pair.of_matrices steane_mat' steane_mat' steane_orth

theorem steane_dist_3 : 3 ≤ steane_css.toBSM.distance (by norm_num) := by
  apply bitvec_sat_translation_correct steane_css steane_ker' steane_ker_mat_correct steane_ker' steane_ker_mat_correct (by norm_num) _ _
  all_goals rw [steane_css, CSS_pair.of_matrices]
  all_goals exact steane_dist
