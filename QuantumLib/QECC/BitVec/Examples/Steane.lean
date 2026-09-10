/-
Copyright (c) 2026 The Lean-QEC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mattias Ehatamm, Yi Lee
-/

import QuantumLib.QECC.BitVec.SAT.Encoding
import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide
import QuantumLib.QECC.BitVec.SAT.Correctness
import QuantumLib.QECC.BitVec.SAT.Distance

/-!
# The Steane code

The `⟦7, 1, 3⟧` CSS code built from the `[7, 4, 3]` Hamming code, together with machine
verification of its rank, orthogonality and distance properties.
-/

set_option maxRecDepth 9999999

namespace QuantumLib

/-- The Hamming checks, packed into a `BitVec` for the SAT encoding. -/
def steane_mat : BitVec (3 * 7) :=
  0x1d2d69

/-- A spanning set of the kernel of `steane_mat`, packed for the SAT encoding. -/
def steane_ker : BitVec (4 * 7) :=
  0x8e94b0b

/-- The parity check matrix of the `[7, 4, 3]` Hamming code. -/
def steane_mat' : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 1, 0, 1, 1;
    0, 1, 0, 1, 1, 0, 1;
    0, 0, 1, 0, 1, 1, 1]

/-- A generator matrix of the Hamming code: its rows span the kernel of `steane_mat'`. -/
def steane_ker' : Matrix (Fin 4) (Fin 7) (ZMod 2) :=
  !![1, 1, 0, 1, 0, 0, 0;
    0, 1, 1, 0, 1, 0, 0;
    1, 0, 1, 0, 0, 1, 0;
    1, 1, 1, 0, 0, 0, 1]

/-- The packed checks are the matrix. -/
lemma steane_mat_correct : steane_mat = flattenMatrix steane_mat' := by decide
/-- The packed kernel generators are the matrix. -/
lemma steane_ker_correct : steane_ker = flattenMatrix steane_ker' := by decide

/-- The Hamming checks are independent, by SAT. -/
lemma steane_ind : LinearIndependent (ZMod 2) steane_mat'.row := by
  rw [linearIndepSAT_correct, ←steane_mat_correct, steane_mat]
  simp only [linearIndepSAT, nonzero, nonzeroAux, Nat.add_one_sub_one, Nat.lt_add_one,
    getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
    Bool.or_eq_true, allDotZero, allDotZeroAux, dotColZero, dotColAux, Nat.reduceMul,
    BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
    Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
    bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  decide

/-- The kernel generators are independent, by SAT. -/
lemma steane_ker_ind : LinearIndependent (ZMod 2) steane_ker'.row := by
  rw [linearIndepSAT_correct, ←steane_ker_correct, steane_ker]
  simp only [linearIndepSAT, nonzero, nonzeroAux, Nat.add_one_sub_one, Nat.lt_add_one,
    getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
    Bool.or_eq_true, allDotZero, allDotZeroAux, dotColZero, dotColAux, Nat.reduceMul,
    BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
    Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
    bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  decide

/-- The Hamming checks have rank `3`. -/
lemma steane_mat_rank : 3 ≤ steane_mat'.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id
  rw [Matrix.submatrix_id_id]
  apply steane_ind

/-- The kernel generators have rank `4`. -/
lemma steane_ker_rank : 4 ≤ steane_ker'.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id
  rw [Matrix.submatrix_id_id]
  apply steane_ker_ind

/-- The Hamming code is self-orthogonal, so it can play both CSS roles. -/
lemma steane_orth : steane_mat'.mutuallyOrthRows steane_mat' := by
  rw [←mutually_orth_nat_correct, ←steane_mat_correct]
  unfold bitVecMutuallyOrthNat
  decide

/-- The kernel generators are orthogonal to the checks. -/
lemma steane_mat_ker_orth : steane_mat'.mutuallyOrthRows steane_ker' := by
  rw [←mutually_orth_nat_correct, ←steane_mat_correct, ←steane_ker_correct]
  unfold bitVecMutuallyOrthNat
  decide

/-- No undetectable error of weight below `3`, by SAT. -/
lemma steane_dist : ltDistSat (flattenMatrix steane_mat') (flattenMatrix steane_ker') 2 3 := by
  rw [←steane_mat_correct, ←steane_ker_correct, steane_mat, steane_ker]
  simp only [ltDistSat, symmetryConstraints, symmetryConstraintsAux, Nat.reduceMul,
    locConstraints, locConstraintsAux, locConstraintsIth, Nat.add_one_sub_one,
    Nat.lt_add_one, getElem!_pos, locConstraintsIthJthAux, locConstraintsIthJth, one_mul,
    Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff, Nat.reduceLT, Nat.one_lt_ofNat,
    Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parityConstraints, parityConstraintsAux,
    BitVec.dotProduct, dotProductAux, BitVec.row, Bool.not_eq_eq_eq_not, Bool.not_true,
    bne_eq_false_iff_eq, decide_eq_true_eq, rowspaceConstraints, rowspaceConstraintsAux,
    not_and, and_imp, bne_iff_ne, ne_eq, not_or, Decidable.not_not]
  bv_check "Steane.lean-steane_dist-94-2.lrat"

/-- The rows of `steane_ker'` span the whole kernel of `steane_mat'`. -/
lemma steane_ker_mat_correct : steane_ker'.isKerFor steane_mat' :=
  Matrix.isKerFor_of_rank_sum_mutuallyOrthRows _ _ steane_mat_rank steane_ker_rank (by norm_num)
    steane_mat_ker_orth

/-- The Steane code: the Hamming checks in both the `X` and the `Z` role. -/
def steane_css : CSSPair 7 3 3 := CSSPair.ofMatrices steane_mat' steane_mat' steane_orth

/-- The Steane code has distance at least `3`. -/
theorem steane_dist_3 : 3 ≤ steane_css.toBSM.distance (by norm_num) := by
  apply bitvec_sat_translation_correct steane_css steane_ker' steane_ker_mat_correct steane_ker'
    steane_ker_mat_correct (by norm_num) _ _
  all_goals rw [steane_css, CSSPair.ofMatrices]
  all_goals exact steane_dist

end QuantumLib
