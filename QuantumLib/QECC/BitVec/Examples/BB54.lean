/-
Copyright (c) 2026 The Lean-QEC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mattias Ehatamm
-/

import QuantumLib.QECC.BitVec.SAT.Encoding
import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide
import QuantumLib.QECC.BitVec.SAT.Correctness
import QuantumLib.QECC.BitVec.Stabilizer.BivariateBicycle
import QuantumLib.QECC.BitVec.SAT.Distance

/-!
# The `⟦54, 8, ≥ 6⟧` bivariate bicycle code

The `l = 3`, `m = 9` bivariate bicycle code of Bravyi et al., with its parity checks given both as
matrices over `ZMod 2` and as the flattened `BitVec`s that the SAT encoding consumes. The rank,
orthogonality and kernel conditions are checked by `bv_check` and `decide`, and the distance bound
is obtained by running `bv_decide` on the encoding of `ltDistSat`.
-/
set_option maxRecDepth 9999999

namespace QuantumLib

/-- The first check polynomial of the code, `A = 1 + y² + y⁴` on the `3 × 9` torus. -/
def BB54_A :=
  let l := 3
  let m := 9
  bb3Matrix l m (true, 0) (false, 2) (false, 4)

/-- The second check polynomial of the code, `B = x + x² + y³` on the `3 × 9` torus. -/
def BB54_B :=
  let l := 3
  let m := 9
  bb3Matrix l m (true, 1) (true, 2) (false, 3)

/-- The `X` parity checks, `[A | B]`. -/
def BB54_X_mat := BB54_A.hstackFin BB54_B

/-- The `Z` parity checks, `[Bᵀ | Aᵀ]`. -/
def BB54_Z_mat := BB54_B.transpose.hstackFin BB54_A.transpose

/-- `BB54_X_mat` flattened row by row into a single `BitVec`. -/
def BB54_X : BitVec (27 * 54) := 0x9008042800000120100850000002402050800008008040a10000100100854000002002010a800000400402150000008008042a000001001008540000800120000850010002400010a00200048000a10004100100014200082002000a800010400400150000208008002a00004100100054000082002000a802010002000010a402000400002148040008000142100820000002842010400000150040208000002a00804100000054010082000000a80201040000015

/-- `BB54_Z_mat` flattened row by row into a single `BitVec`. -/
def BB54_Z : BitVec (27 * 54) := 0x2a00000082010054000001040200a800000208040150000004100802a00000082010850000001040210a00004000804a100000800100942000010002010054001001040000a800200208000150004004100002a00080082000054001001040010a000200208002140004800100142000090002002840001200040000a840200200000150804004000002a10080080000054201001000000a8402002000021408040040000428100900000028402012000000508040240

/-- Thirty-one vectors spanning the kernel of `BB54_X_mat`, flattened into a single `BitVec`. -/
def BB54_X_ker : BitVec (31 * 54) := 0x20000019e8a47940000046f3d800800000968a00010000067f3d144200001000de140400002002d028080001948fe5401000047b001ec02000094000500040006523d1e40080011ecde000010002502d0000020019e8fe5100040046f00050000800968000a00010067f29150000201000f67b00004020028140000081948a45100001047b3d850000020940a00a00000467a3d1500000091bcde7b00000125a2d1400000039fcfe7900000016d0000000000036c0000000000000b6800000000001b600000000000005b400000000000db

/-- Thirty-one vectors spanning the kernel of `BB54_Z_mat`, flattened into a single `BitVec`. -/
def BB54_Z_ker : BitVec (31 * 54) := 0x20001008cc288640004023d16d008001008e82a8710004021d049002001008a80e07040040215000000801008b84f03010040217082080201008bc5f4200404003b0e710008100008240200104003a0af14002100098650200044002802d140009000bc7542000140008009040003000fc71c000002023b1df8c000040808041200000823a1d7a80000108984d16000002228145a00000048bc5f57000000a08041200000018fc7fc7000000124004900000002480092000000049001240000000024924000000000492480000000009249

/-- Twenty-three rows of `BB54_X_mat` that are linearly independent. -/
def BB54indrowsx : Fin 23 → Fin 27 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19, 20, 21, 22, 23, 24]

/-- Twenty-three rows of `BB54_Z_mat` that are linearly independent. -/
def BB54indrowsz : Fin 23 → Fin 27 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19, 20, 21, 22, 23, 24]

/-- The rows `BB54indrowsx` of `BB54_X_mat`, flattened into a single `BitVec`. -/
def BB54_X_submat : BitVec (23 * 54) := 0x2402050800008008040a10000100100854000002002010a800000400402150000008008042a000001001008540000200048000a10004100100014200082002000a800010400400150000208008002a00004100100054000082002000a802010002000010a402000400002148040008000142100820000002842010400000150040208000002a00804100000054010082000000a80201040000015

set_option exponentiation.threshold 10000 in
/-- `BB54_X_submat` really is that submatrix. -/
lemma BB54_X_submat_correct : BB54_X_submat = flattenMatrix (BB54_X_mat.submatrix BB54indrowsx id) := by decide

/-- The rows `BB54indrowsz` of `BB54_Z_mat`, flattened into a single `BitVec`. -/
def BB54_Z_submat : BitVec (23 * 54) := 0xa800000208040150000004100802a00000082010850000001040210a00004000804a1000008001009420000100020100150004004100002a00080082000054001001040010a000200208002140004800100142000090002002840001200040000a840200200000150804004000002a10080080000054201001000000a8402002000021408040040000428100900000028402012000000508040240

set_option exponentiation.threshold 10000 in
/-- `BB54_Z_submat` really is that submatrix. -/
lemma BB54_Z_submat_correct : BB54_Z_submat = flattenMatrix (BB54_Z_mat.submatrix BB54indrowsz id) := by decide

/-- The spanning set `BB54_X_ker` of the kernel of `BB54_X_mat`, as a matrix. -/
def BB54_X_ker_mat := BitVecMatrix BB54_X_ker

/-- The spanning set `BB54_Z_ker` of the kernel of `BB54_Z_mat`, as a matrix. -/
def BB54_Z_ker_mat := BitVecMatrix BB54_Z_ker

/-- `BB54_X_ker_mat` flattens back to `BB54_X_ker`. -/
lemma BB54_X_ker_mat_correct : flattenMatrix BB54_X_ker_mat = BB54_X_ker := flatten_BitVecMatrix_id _

/-- `BB54_Z_ker_mat` flattens back to `BB54_Z_ker`. -/
lemma BB54_Z_ker_mat_correct : flattenMatrix BB54_Z_ker_mat = BB54_Z_ker := flatten_BitVecMatrix_id _

set_option exponentiation.threshold 10000 in
/-- `BB54_X` really is the flattening of `BB54_X_mat`. -/
lemma BB54_X_correct : BB54_X = flattenMatrix BB54_X_mat := by decide

set_option exponentiation.threshold 10000 in
/-- `BB54_Z` really is the flattening of `BB54_Z_mat`. -/
lemma BB54_Z_correct : BB54_Z = flattenMatrix BB54_Z_mat := by decide

set_option maxHeartbeats 0 in
/-- The `X` checks have rank at least `23`: the rows `BB54indrowsx` are independent. -/
lemma BB54_X_rank : 23 ≤ BB54_X_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ BB54indrowsx
  rw [linearIndepSAT_correct,  ←BB54_X_submat_correct, BB54_X_submat]
  simp only [linearIndepSAT, nonzero, nonzeroAux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, allDotZero, allDotZeroAux, dotColZero, dotColAux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq, Nat.succ_eq_add_one]
  bv_check "BB54.lean-BB54_X_rank-66-2.lrat"

set_option maxHeartbeats 0 in
/-- The `Z` checks have rank at least `23`: the rows `BB54indrowsz` are independent. -/
lemma BB54_Z_rank : 23 ≤ BB54_Z_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ BB54indrowsz
  rw [linearIndepSAT_correct,  ←BB54_Z_submat_correct, BB54_Z_submat]
  simp only [linearIndepSAT, nonzero, nonzeroAux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, allDotZero, allDotZeroAux, dotColZero, dotColAux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq, Nat.succ_eq_add_one]
  bv_check "BB54.lean-BB54_Z_rank-78-2.lrat"

set_option maxHeartbeats 0 in
/-- The kernel vectors of `BB54_X_mat` have rank at least `31`. -/
lemma BB54_X_ker_rank : 31 ≤ BB54_X_ker_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id
  rw [Matrix.submatrix_id_id]
  rw [linearIndepSAT_correct, BB54_X_ker_mat_correct, BB54_X_ker]
  simp only [linearIndepSAT, nonzero, nonzeroAux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, allDotZero, allDotZeroAux, dotColZero, dotColAux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq, Nat.succ_eq_add_one]
  bv_normalize

set_option maxHeartbeats 0 in
/-- The kernel vectors of `BB54_Z_mat` have rank at least `31`. -/
lemma BB54_Z_ker_rank : 31 ≤ BB54_Z_ker_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id
  rw [Matrix.submatrix_id_id]
  rw [linearIndepSAT_correct, BB54_Z_ker_mat_correct, BB54_Z_ker]
  simp only [linearIndepSAT, nonzero, nonzeroAux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, allDotZero, allDotZeroAux, dotColZero, dotColAux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq, Nat.succ_eq_add_one]
  bv_normalize

set_option exponentiation.threshold 10000 in
set_option maxHeartbeats 0 in
/-- The `X` and the `Z` checks commute. -/
lemma BB54_XZ_orth : BB54_X_mat.mutuallyOrthRows BB54_Z_mat := by
  rw [←mutually_orth_nat_correct, ←BB54_X_correct, ←BB54_Z_correct]
  unfold bitVecMutuallyOrthNat
  decide

set_option exponentiation.threshold 10000 in
set_option maxHeartbeats 0 in
/-- Every vector of `BB54_X_ker_mat` is orthogonal to every `X` check. -/
lemma BB54_X_ker_orth : BB54_X_mat.mutuallyOrthRows BB54_X_ker_mat := by
  rw [←mutually_orth_nat_correct, ←BB54_X_correct, BB54_X_ker_mat_correct]
  unfold bitVecMutuallyOrthNat
  decide

set_option exponentiation.threshold 10000 in
set_option maxHeartbeats 0 in
/-- Every vector of `BB54_Z_ker_mat` is orthogonal to every `Z` check. -/
lemma BB54_Z_ker_orth : BB54_Z_mat.mutuallyOrthRows BB54_Z_ker_mat := by
  rw [←mutually_orth_nat_correct, ←BB54_Z_correct, BB54_Z_ker_mat_correct]
  unfold bitVecMutuallyOrthNat
  decide

set_option maxHeartbeats 0 in
/-- Half of the distance bound: the encoding of "some undetectable error has weight at most `5`"
for the `X` checks, against the kernel of the `Z` checks, is unsatisfiable. -/
lemma BB54_dist_z : ltDistSat BB54_X BB54_Z_ker 5 6 := by
  rw [BB54_X, BB54_Z_ker]
  simp (maxSteps := 9999999) only [ltDistSat, Nat.reduceMul, locConstraints, locConstraintsAux,
    locConstraintsIth, symmetryConstraints, symmetryConstraintsAux, Nat.add_one_sub_one,
    Nat.lt_add_one, getElem!_pos, locConstraintsIthJthAux, locConstraintsIthJth, one_mul,
    Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff, Nat.reduceLT, Nat.one_lt_ofNat,
    Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parityConstraints, parityConstraintsAux,
    BitVec.dotProduct, dotProductAux, BitVec.row, Bool.not_eq_eq_eq_not, Bool.not_true,
    bne_eq_false_iff_eq, decide_eq_true_eq, rowspaceConstraints, rowspaceConstraintsAux,
    not_and, and_imp]
  bv_decide (timeout := 9999) (maxSteps := 9999999)

set_option maxHeartbeats 0 in
/-- Half of the distance bound: the encoding of "some undetectable error has weight at most `5`"
for the `Z` checks, against the kernel of the `X` checks, is unsatisfiable. -/
lemma BB54_dist_x : ltDistSat BB54_Z BB54_X_ker 5 6 := by
  rw [BB54_Z, BB54_X_ker]
  simp (maxSteps := 9999999) only [ltDistSat, Nat.reduceMul, locConstraints, locConstraintsAux,
    locConstraintsIth, symmetryConstraints, symmetryConstraintsAux, Nat.add_one_sub_one,
    Nat.lt_add_one, getElem!_pos, locConstraintsIthJthAux, locConstraintsIthJth, one_mul,
    Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff, Nat.reduceLT, Nat.one_lt_ofNat,
    Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parityConstraints, parityConstraintsAux,
    BitVec.dotProduct, dotProductAux, BitVec.row, Bool.not_eq_eq_eq_not, Bool.not_true,
    bne_eq_false_iff_eq, decide_eq_true_eq, rowspaceConstraints, rowspaceConstraintsAux,
    not_and, and_imp]
  bv_decide (timeout := 9999) (maxSteps := 9999999)

/-- `BB54_X_ker_mat` spans the whole kernel of `BB54_X_mat`, since `23 + 31 = 54`. -/
lemma BB54_X_ker_is_ker : BB54_X_ker_mat.isKerFor BB54_X_mat := by
  apply Matrix.isKerFor_of_rank_sum_mutuallyOrthRows _ _ BB54_X_rank BB54_X_ker_rank
    (by norm_num) BB54_X_ker_orth

/-- `BB54_Z_ker_mat` spans the whole kernel of `BB54_Z_mat`, since `23 + 31 = 54`. -/
lemma BB54_Z_ker_is_ker : BB54_Z_ker_mat.isKerFor BB54_Z_mat := by
  apply Matrix.isKerFor_of_rank_sum_mutuallyOrthRows _ _ BB54_Z_rank BB54_Z_ker_rank
    (by norm_num) BB54_Z_ker_orth

/-- The code, as a pair of commuting CSS check matrices. -/
def BB54_css : CSSPair 54 27 27 :=
  CSSPair.ofMatrices BB54_X_mat BB54_Z_mat BB54_XZ_orth

/-- The code has distance at least `6`. -/
theorem BB54_dist_6 : 6 ≤ BB54_css.toBSM.distance (by norm_num) := by
  apply bitvec_sat_translation_correct BB54_css
      BB54_Z_ker_mat BB54_Z_ker_is_ker
      BB54_X_ker_mat BB54_X_ker_is_ker (by norm_num) _ _
  · rw [BB54_css, CSSPair.ofMatrices, ←BB54_X_correct, BB54_Z_ker_mat_correct]
    exact BB54_dist_z
  rw [BB54_css, CSSPair.ofMatrices, ←BB54_Z_correct, BB54_X_ker_mat_correct]
  exact BB54_dist_x

end QuantumLib
