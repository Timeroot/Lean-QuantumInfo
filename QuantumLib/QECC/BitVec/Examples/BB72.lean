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
# The `⟦72, 12, ≥ 6⟧` bivariate bicycle code

The `l = m = 6` bivariate bicycle code of Bravyi et al., handled exactly as `BB54`: parity checks
as matrices over `ZMod 2` and as flattened `BitVec`s, rank and orthogonality by `bv_check` and
`decide`, and the distance bound by `bv_decide` on the encoding of `ltDistSat`.
-/
set_option maxRecDepth 9999999

namespace QuantumLib

/-- The first check polynomial of the code, `A = x³ + y + y²` on the `6 × 6` torus. -/
def BB72_A :=
  let l := 6
  let m := 6
  bb3Matrix l m (true, 3) (false, 1) (false, 2)

/-- The second check polynomial of the code, `B = x + x² + y³` on the `6 × 6` torus. -/
def BB72_B :=
  let l := 6
  let m := 6
  bb3Matrix l m (true, 1) (true, 2) (false, 3)

/-- The `X` parity checks, `[A | B]`. -/
def BB72_X_mat := BB72_A.hstackFin BB72_B

/-- The `Z` parity checks, `[Bᵀ | Aᵀ]`. -/
def BB72_Z_mat := BB72_B.transpose.hstackFin BB72_A.transpose

/-- `BB72_X_mat` flattened row by row into a single `BitVec`. -/
def BB72_X : BitVec (36 * 72) := 0x1000008200c0020000080000410840010000040000208c0000800080000010460000400040000008230000200020000004118000100080400002000300080040200001002100040020100000803000020012000000401800010009000000200c0000800480000010060000408201000000000c0020410080000000840010208040000000c0000810480000000060000408240000000030000204120000000018000102080400080000300001040200040002100000820100020003000000412000010001800000209000008000c0000010480000400060000008201000200000c0000410080010000840000208040008000c0000010480000400060000008240000200030000004120000100018000002080400080000300001040200040002100000820100020003000000412000010001800000209000008000c000001048000040006

/-- `BB72_Z_mat` flattened row by row into a single `BitVec`. -/
def BB72_Z : BitVec (36 * 72) := 0x6000200001208000003000100000904000001800080000482000000c0004000804100000840002000402080000c0000100020104000001800080000482000000c0004000024100000060002000012080000030001000201040000210000800100820000300000400080410000006000200001208000003000100000904000001800080000482000000c0004000804100000840002000402080000c0000100020104080001800000000482040000c0000000024102000060000000012081000030000000201040800210000000100820400300000000080410200006008000001200100003004000000900080001802000000480040000c0100000804002000840080000402001000c0004000020100080001882000000400040000c410000002000200006208000001000100003104000020000080021082000010000040030041000008

/-- Forty-two vectors spanning the kernel of `BB72_X_mat`, flattened into a single `BitVec`. -/
def BB72_X_ker : BitVec (42 * 72) := 0x8000000860020801c14000000430010408e02000000c20030406f81000000880c103bf040800000440c20049c20400000cb0030806e00200000ce0430bd6c101000008e0410fcf010080000470820e79d90040000c00400338040020000890420bbe2300100004e04203f9c100080000d0410bdf6500040000c04103cf020002000060820279c1000100003041033ce000008000b04107bee000004000f0410fffd90000200810400b306100001004a04303b6c00000080cc0410bff2100000408f0400fd3d100000204d0430bc7210000010c50820a79210000008c90c20bba210000004870c00841e10000002490030006000000001c70020c099100000002a0c307bef00000000150c308412100000000088003900000000000044003c000000000000280027000000000000140033000000000000022000e40000000000011000f0000000000000a0009c0000000000005000cc000000000000088003900000000000044003c000000000000280027000000000000140033

/-- Forty-two vectors spanning the kernel of `BB72_Z_mat`, flattened into a single `BitVec`. -/
def BB72_Z_ker : BitVec (42 * 72) := 0x80000004e0000c2524400000082000863b61200000041000c31db010000008800061a44608000004400030da03040000087000184cd202000008c0000013450100000460000209a2008000086000032d2200400004300001969100200008900000e1f60010000490000073b60008000cb0000032d30004000cd000003bf70002000ce000003f650001000c20000036410000800c40000032d30000400c700000309a0000200810008229f000001004d0004117b500000808e00020a16400000404700010589200000208b0000806d70000010480000400060000008850000229f300000044f00001179400000028f00000a15400000014a0000053e700000002d000000b6d00000001b0000006db000000000800104904000000000400082482000000000200041241000000000100820920000000000080410490000000000040208248000000000020824804000000000010412402000000000008209201000000000004124120000000000002092090000000000001049048

/-- Thirty rows of `BB72_X_mat` that are linearly independent. -/
def BB72indrowsx : Fin 30 → Fin 36 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 30, 31]

/-- Thirty rows of `BB72_Z_mat` that are linearly independent. -/
def BB72indrowsz : Fin 30 → Fin 36 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 30, 31]

/-- The rows `BB72indrowsx` of `BB72_X_mat`, flattened into a single `BitVec`. -/
def BB72_X_submat : BitVec (30 * 72) := 0x40000008230000200020000004118000100020100000803000020012000000401800010009000000200c0000800480000010060000408201000000000c0020410080000000840010208040000000c0000810480000000060000408240000000030000204120000000018000102080400080000300001040200040002100000820100020003000000412000010001800000209000008000c0000010480000400060000008201000200000c0000410080010000840000208040008000c0000010480000400060000008240000200030000004120000100018000002080400080000300001040200040002100000820100020003000000412000010001800000209000008000c000001048000040006

set_option exponentiation.threshold 10000 in
/-- `BB72_X_submat` really is that submatrix. -/
lemma BB72_X_submat_correct : BB72_X_submat = flattenMatrix (BB72_X_mat.submatrix BB72indrowsx id) := by decide

/-- The rows `BB72indrowsz` of `BB72_Z_mat`, flattened into a single `BitVec`. -/
def BB72_Z_submat : BitVec (30 * 72) := 0x840002000402080000c000010002010400000060002000012080000030001000201040000210000800100820000300000400080410000006000200001208000003000100000904000001800080000482000000c0004000804100000840002000402080000c0000100020104080001800000000482040000c0000000024102000060000000012081000030000000201040800210000000100820400300000000080410200006008000001200100003004000000900080001802000000480040000c0100000804002000840080000402001000c0004000020100080001882000000400040000c410000002000200006208000001000100003104000020000080021082000010000040030041000008

set_option exponentiation.threshold 10000 in
/-- `BB72_Z_submat` really is that submatrix. -/
lemma BB72_Z_submat_correct : BB72_Z_submat = flattenMatrix (BB72_Z_mat.submatrix BB72indrowsz id) := by decide

/-- The spanning set `BB72_X_ker` of the kernel of `BB72_X_mat`, as a matrix. -/
def BB72_X_ker_mat := BitVecMatrix BB72_X_ker

/-- The spanning set `BB72_Z_ker` of the kernel of `BB72_Z_mat`, as a matrix. -/
def BB72_Z_ker_mat := BitVecMatrix BB72_Z_ker

/-- `BB72_X_ker_mat` flattens back to `BB72_X_ker`. -/
lemma BB72_X_ker_mat_correct : flattenMatrix BB72_X_ker_mat = BB72_X_ker := flatten_BitVecMatrix_id _

/-- `BB72_Z_ker_mat` flattens back to `BB72_Z_ker`. -/
lemma BB72_Z_ker_mat_correct : flattenMatrix BB72_Z_ker_mat = BB72_Z_ker := flatten_BitVecMatrix_id _

set_option exponentiation.threshold 10000 in
/-- `BB72_X` really is the flattening of `BB72_X_mat`. -/
lemma BB72_X_correct : BB72_X = flattenMatrix BB72_X_mat := by decide

set_option exponentiation.threshold 10000 in
/-- `BB72_Z` really is the flattening of `BB72_Z_mat`. -/
lemma BB72_Z_correct : BB72_Z = flattenMatrix BB72_Z_mat := by decide

set_option maxHeartbeats 0 in
/-- The `X` checks have rank at least `30`: the rows `BB72indrowsx` are independent. -/
lemma BB72_X_rank : 30 ≤ BB72_X_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ BB72indrowsx
  rw [linearIndepSAT_correct,  ←BB72_X_submat_correct, BB72_X_submat]
  simp only [linearIndepSAT, nonzero, nonzeroAux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, allDotZero, allDotZeroAux, dotColZero, dotColAux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq, Nat.succ_eq_add_one]
  bv_check "BB72.lean-BB72_X_rank-67-2.lrat"

set_option maxHeartbeats 0 in
/-- The `Z` checks have rank at least `30`: the rows `BB72indrowsz` are independent. -/
lemma BB72_Z_rank : 30 ≤ BB72_Z_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ BB72indrowsz
  rw [linearIndepSAT_correct,  ←BB72_Z_submat_correct, BB72_Z_submat]
  simp only [linearIndepSAT, nonzero, nonzeroAux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, allDotZero, allDotZeroAux, dotColZero, dotColAux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq, Nat.succ_eq_add_one]
  bv_check "BB72.lean-BB72_Z_rank-79-2.lrat"

set_option maxHeartbeats 0 in
/-- The kernel vectors of `BB72_X_mat` have rank at least `42`. -/
lemma BB72_X_ker_rank : 42 ≤ BB72_X_ker_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id
  rw [Matrix.submatrix_id_id]
  rw [linearIndepSAT_correct, BB72_X_ker_mat_correct, BB72_X_ker]
  simp only [linearIndepSAT, nonzero, nonzeroAux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, allDotZero, allDotZeroAux, dotColZero, dotColAux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq, Nat.succ_eq_add_one]
  bv_normalize

set_option maxHeartbeats 0 in
/-- The kernel vectors of `BB72_Z_mat` have rank at least `42`. -/
lemma BB72_Z_ker_rank : 42 ≤ BB72_Z_ker_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id
  rw [Matrix.submatrix_id_id]
  rw [linearIndepSAT_correct, BB72_Z_ker_mat_correct, BB72_Z_ker]
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
lemma BB72_XZ_orth : BB72_X_mat.mutuallyOrthRows BB72_Z_mat := by
  rw [←mutually_orth_nat_correct, ←BB72_X_correct, ←BB72_Z_correct]
  unfold bitVecMutuallyOrthNat
  decide

set_option exponentiation.threshold 10000 in
set_option maxHeartbeats 0 in
/-- Every vector of `BB72_X_ker_mat` is orthogonal to every `X` check. -/
lemma BB72_X_ker_orth : BB72_X_mat.mutuallyOrthRows BB72_X_ker_mat := by
  rw [←mutually_orth_nat_correct, ←BB72_X_correct, BB72_X_ker_mat_correct]
  unfold bitVecMutuallyOrthNat
  decide

set_option exponentiation.threshold 10000 in
set_option maxHeartbeats 0 in
/-- Every vector of `BB72_Z_ker_mat` is orthogonal to every `Z` check. -/
lemma BB72_Z_ker_orth : BB72_Z_mat.mutuallyOrthRows BB72_Z_ker_mat := by
  rw [←mutually_orth_nat_correct, ←BB72_Z_correct, BB72_Z_ker_mat_correct]
  unfold bitVecMutuallyOrthNat
  decide

set_option maxHeartbeats 0 in
/-- Half of the distance bound: the encoding of "some undetectable error has weight at most `5`"
for the `X` checks, against the kernel of the `Z` checks, is unsatisfiable. -/
lemma BB72_dist_z : ltDistSat BB72_X BB72_Z_ker 5 7 := by
  rw [BB72_X, BB72_Z_ker]
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
lemma BB72_dist_x : ltDistSat BB72_Z BB72_X_ker 5 7 := by
  rw [BB72_Z, BB72_X_ker]
  simp (maxSteps := 9999999) only [ltDistSat, Nat.reduceMul, locConstraints, locConstraintsAux,
    locConstraintsIth, symmetryConstraints, symmetryConstraintsAux, Nat.add_one_sub_one,
    Nat.lt_add_one, getElem!_pos, locConstraintsIthJthAux, locConstraintsIthJth, one_mul,
    Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff, Nat.reduceLT, Nat.one_lt_ofNat,
    Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parityConstraints, parityConstraintsAux,
    BitVec.dotProduct, dotProductAux, BitVec.row, Bool.not_eq_eq_eq_not, Bool.not_true,
    bne_eq_false_iff_eq, decide_eq_true_eq, rowspaceConstraints, rowspaceConstraintsAux,
    not_and, and_imp]
  bv_decide (timeout := 9999) (maxSteps := 9999999)

/-- `BB72_X_ker_mat` spans the whole kernel of `BB72_X_mat`, since `30 + 42 = 72`. -/
lemma BB72_X_ker_is_ker : BB72_X_ker_mat.isKerFor BB72_X_mat := by
  apply Matrix.isKerFor_of_rank_sum_mutuallyOrthRows _ _ BB72_X_rank BB72_X_ker_rank
    (by norm_num) BB72_X_ker_orth

/-- `BB72_Z_ker_mat` spans the whole kernel of `BB72_Z_mat`, since `30 + 42 = 72`. -/
lemma BB72_Z_ker_is_ker : BB72_Z_ker_mat.isKerFor BB72_Z_mat := by
  apply Matrix.isKerFor_of_rank_sum_mutuallyOrthRows _ _ BB72_Z_rank BB72_Z_ker_rank
    (by norm_num) BB72_Z_ker_orth

/-- The code, as a pair of commuting CSS check matrices. -/
def BB72_css : CSSPair 72 36 36 :=
  CSSPair.ofMatrices BB72_X_mat BB72_Z_mat BB72_XZ_orth

/-- The code has distance at least `6`. -/
theorem BB72_dist_6 : 6 ≤ BB72_css.toBSM.distance (by norm_num) := by
  apply bitvec_sat_translation_correct BB72_css
      BB72_Z_ker_mat BB72_Z_ker_is_ker
      BB72_X_ker_mat BB72_X_ker_is_ker (by norm_num) _ _
  · rw [BB72_css, CSSPair.ofMatrices, ←BB72_X_correct, BB72_Z_ker_mat_correct]
    exact BB72_dist_z
  rw [BB72_css, CSSPair.ofMatrices, ←BB72_Z_correct, BB72_X_ker_mat_correct]
  exact BB72_dist_x

end QuantumLib
