import LeanQEC.ComputerAlgebra.BitVecSAT
import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide
import LeanQEC.ComputerAlgebra.BitVecCorrectness
import LeanQEC.Stabilizer.BB
import LeanQEC.Stabilizer.BitVecSATToDist
import LeanQEC.timedbv
set_option maxRecDepth 9999999
def BB90_A :=
  let l := 15
  let m := 3
  BB3_matrix l m (true, 9) (false, 1) (false, 2)
def BB90_B :=
  let l := 15
  let m := 3
  BB3_matrix l m (false, 0) (true, 2) (true, 7)
def BB90_X_mat := BB90_A.hstack_fin BB90_B
def BB90_Z_mat := BB90_B.transpose.hstack_fin BB90_A.transpose
def BB90_X : BitVec (45 * 90) := 0x200000200040c0004000000400000400085000080000008000008001180001000000100000100020600020000002000002000428000400000040000040008c00008000020800000800003000100000410000010000140002000008200000200006000040000104000004000018000800002080000080000a000100000410000010000300002000008200000200000c0004000010400000400005000080000208000008000180001000004100000100000600020000082000002000028000400001040000040000c00008000020800000800003000100000410000010000140002000008200000200006000040800104000000000018000810002080000000000a000102000410000000000300002040008200000000000c0004080010400000000005000081000208000000000180001020004100004000000600000400082000080000028000008001040001000000c00000100020800020000003000002000410000400000140000040008200008000006000000800104000100000018000010002080002000000a000002000410000400000300000040008200008000000c0000080010400010000005000001000208000200000180000020004100004000000600000400082000080000028000008001040001000000c00000100020800020000003000002000410000400000140000040008200008000006
def BB90_Z : BitVec (45 * 90) := 0x18000004000104000800000a000000800020800100000300000010000410002000000c0000020000820004000005000000400010400080000180000008000208001000000600000100004100020000028000002000082000400000c00000040001040008000003000000800020800100000140000010000410002000006000000200008200040000018000004000104000800000a000000800020800100000300000010000410002000000c0000020000820004000005000000400010400080000180000008000208001020000600000000004100020400028000000000082000408000c00000000001040008100003000000000020800102000140000000000410002040006000000000008200040800018000100000104000010000a000020000020800002000300000400000410000040000c0000800000820000080005000010000010400001000180000200000208000020000600004000004100000400028000080000082000008000c00001000001040000100003000020000020800002000140000400000410000040006000008000008200000800018000100000104000010000a000020000020800002000300000400000410000040000c4000800000800000080005080010000010000001000181000200000200000020000620004000004000000400028400080000080000008000c08001000001
def BB90_X_ker : BitVec (49 * 90) := 0x2000000000060000470003b400000000010000e92007f480000000002000392401fe100000000018018038e03102000000000400a38038082040000000008030e00e01040800000000640ac672f15b01000000001101df927c4b402000000002401be2471f600400000001821d628f7ba00080000000408ad083be98001000000008230238e390000200000006010e8787bde0004000000100458161d8b800080000002011b838703600010000001803861803be00002000000400e10400eb8000040000008038208039e000008000006001c06001dc000010000010007e10000a800002000002001f8200031000004000019028f98a05e00000080000440606418138000001000009000188007e00000020000608144a0502c000000400010203ea00c7680000008000208039e001c1000000100019068bbea2d180000002000441626198706000000040009040f86007180000000800608f40b050eb00000001001023be220c2740000000200208e38e4004600000000401805fa1ee2b780000000080401be05b86ae000000001008077e0ee01d80000000020600ef86070d800000000041003d0101c2a00000000008200f802070700000000001180077180386000000000024001d2400fe800000000004800724803fc00000000000e00038e001c0000000000005028140a050000000000000c06030180c0000000000000a05028140a000000000000180c0603018000000000000140a050281400000000000030180c0603
def BB90_Z_ker : BitVec (49 * 90) := 0x200000000012015404a28f6400000000048063024515d88000000001201e00fcf3b61000000000401c27bbaecb8200000000100712ef5d69e0400000000401c7dbe181180800000000206225c6dae30100000000081884f16dd540200000000206208c4018e0040000000480917d26b8a4008000000120486f92ce190010000000481f9dffdf80400200000010008821144320004000000400141028a0d000080000010003c7079e37000100000008094092cb0100002000000204884934c020000400000081f91ffdf0040000800001205284a79f320000100000480cc099e7ad000002000012003c1079e770000040000400c1098413480000080001005044a209640000010000401811f0e3efc000002000020221a452418000000400008108b21920a00000008000207237e7fe300000001000480690ed15cd400000020012016456c3ab3000000040048041180031c000000008010047659cf2150000000100400ab4d73c88c0000000201001c083cf23800000000400814b0694541c000000008020334166188700000000100800e041e791c0000000021206a67d7ded10000000004481995f3efd84000000000920604fc38fb9000000000140005140a28b400000000030000c301861b00000000002816816db680000000000006036036db600000000000004120904824100000000000082412090482000000000001048241209040000000000024120904824000000000000482412090480000000000009048241209
def BB90indrowsx : Fin 41 → Fin 45 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 42]
lemma BB90StrictMono_indrowsx : StrictMono BB90indrowsx := by decide
def BB90indrowsz : Fin 41 → Fin 45 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 42]
lemma BB90StrictMono_indrowsz : StrictMono BB90indrowsz := by decide
def BB90_X_submat : BitVec (41 * 90) := 0x8000008001180001000000040000040008c00008000020800000800003000100000410000010000140002000008200000200006000040000104000004000018000800002080000080000a000100000410000010000300002000008200000200000c0004000010400000400005000080000208000008000180001000004100000100000600020000082000002000028000400001040000040000c00008000020800000800003000100000410000010000140002000008200000200006000040800104000000000018000810002080000000000a000102000410000000000300002040008200000000000c0004080010400000000005000081000208000000000180001020004100004000000600000400082000080000028000008001040001000000c00000100020800020000003000002000410000400000140000040008200008000006000000800104000100000018000010002080002000000a000002000410000400000300000040008200008000000c0000080010400010000005000001000208000200000180000020004100004000000600000400082000080000028000008001040001000000c00000100020800020000003000002000410000400000140000040008200008000006
set_option exponentiation.threshold 10000 in
lemma BB90_X_submat_correct : BB90_X_submat = flatten_matrix (BB90_X_mat.submatrix BB90indrowsx id) := by decide
def BB90_Z_submat : BitVec (41 * 90) := 0x30000001000041000200000180000008000208001000000600000100004100020000028000002000082000400000c00000040001040008000003000000800020800100000140000010000410002000006000000200008200040000018000004000104000800000a000000800020800100000300000010000410002000000c0000020000820004000005000000400010400080000180000008000208001020000600000000004100020400028000000000082000408000c00000000001040008100003000000000020800102000140000000000410002040006000000000008200040800018000100000104000010000a000020000020800002000300000400000410000040000c0000800000820000080005000010000010400001000180000200000208000020000600004000004100000400028000080000082000008000c00001000001040000100003000020000020800002000140000400000410000040006000008000008200000800018000100000104000010000a000020000020800002000300000400000410000040000c4000800000800000080005080010000010000001000181000200000200000020000620004000004000000400028400080000080000008000c08001000001
set_option exponentiation.threshold 10000 in
lemma BB90_Z_submat_correct : BB90_Z_submat = flatten_matrix (BB90_Z_mat.submatrix BB90indrowsz id) := by decide
def BB90_X_ker_mat := BitVecMatrix BB90_X_ker
def BB90_Z_ker_mat := BitVecMatrix BB90_Z_ker
lemma BB90_X_ker_mat_correct : flatten_matrix BB90_X_ker_mat = BB90_X_ker := flatten_BitVecMatrix_id _
lemma BB90_Z_ker_mat_correct : flatten_matrix BB90_Z_ker_mat = BB90_Z_ker := flatten_BitVecMatrix_id _
set_option exponentiation.threshold 10000 in
lemma BB90_X_correct : BB90_X = flatten_matrix BB90_X_mat := by decide
set_option exponentiation.threshold 10000 in
lemma BB90_Z_correct : BB90_Z = flatten_matrix BB90_Z_mat := by decide
set_option maxHeartbeats 0 in
lemma BB90_X_rank : 41 ≤ BB90_X_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ BB90indrowsx BB90StrictMono_indrowsx
  rw [linear_indep_SAT_correct,  ←BB90_X_submat_correct, BB90_X_submat]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide (timeout := 9999) (maxSteps := 9999999)
set_option maxHeartbeats 0 in
lemma BB90_Z_rank : 41 ≤ BB90_Z_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ BB90indrowsz BB90StrictMono_indrowsx
  rw [linear_indep_SAT_correct,  ←BB90_Z_submat_correct, BB90_Z_submat]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide (timeout := 9999) (maxSteps := 9999999)
set_option maxHeartbeats 0 in
lemma BB90_X_ker_rank : 49 ≤ BB90_X_ker_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)
  rw [Matrix.submatrix_id_id]
  rw [linear_indep_SAT_correct, BB90_X_ker_mat_correct, BB90_X_ker]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide (timeout := 9999) (maxSteps := 9999999)
set_option maxHeartbeats 0 in
lemma BB90_Z_ker_rank : 49 ≤ BB90_Z_ker_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)
  rw [Matrix.submatrix_id_id]
  rw [linear_indep_SAT_correct, BB90_Z_ker_mat_correct, BB90_Z_ker]
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
lemma BB90_XZ_orth : BB90_X_mat.mutually_orth_rows BB90_Z_mat := by
  rw [←mutually_orth_nat_correct, ←BB90_X_correct, ←BB90_Z_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option exponentiation.threshold 10000
set_option maxHeartbeats 0
lemma BB90_X_ker_orth : BB90_X_mat.mutually_orth_rows BB90_X_ker_mat := by
  rw [←mutually_orth_nat_correct, ←BB90_X_correct, BB90_X_ker_mat_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option exponentiation.threshold 10000
set_option maxHeartbeats 0
lemma BB90_Z_ker_orth : BB90_Z_mat.mutually_orth_rows BB90_Z_ker_mat := by
  rw [←mutually_orth_nat_correct, ←BB90_Z_correct, BB90_Z_ker_mat_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option maxHeartbeats 0 in
lemma BB90_dist_z : lt_dist_sat BB90_X BB90_Z_ker 9 7 := by
  rw [BB90_X, BB90_Z_ker]
  simp (maxSteps := 9999999) only [lt_dist_sat, Nat.reduceMul, loc_constraints, loc_constraints_aux, loc_constraints_ith,
  symmetry_constraints, symmetry_constraints_aux,  Nat.add_one_sub_one, Nat.lt_add_one, getElem!_pos, loc_constraints_ith_jth_aux,
  loc_constraints_ith_jth, one_mul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff,
  Nat.reduceLT, Nat.one_lt_ofNat, Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, dot_product_aux, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  bv_decidet "bvd_times.csv" (timeout := 9999) (maxSteps := 9999999)
set_option maxHeartbeats 0 in
lemma BB90_dist_x : lt_dist_sat BB90_Z BB90_X_ker 9 7 := by
  rw [BB90_Z, BB90_X_ker]
  simp (maxSteps := 9999999) only [lt_dist_sat, Nat.reduceMul, loc_constraints, loc_constraints_aux, loc_constraints_ith,
  symmetry_constraints, symmetry_constraints_aux,  Nat.add_one_sub_one, Nat.lt_add_one, getElem!_pos, loc_constraints_ith_jth_aux,
  loc_constraints_ith_jth, one_mul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff,
  Nat.reduceLT, Nat.one_lt_ofNat, Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, dot_product_aux, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  sorry
  --bv_decide (timeout := 9999) (maxSteps := 9999999)
lemma BB90_X_ker_is_ker : BB90_X_ker_mat.is_ker_for BB90_X_mat := by
  apply Matrix.is_ker_for_of_rank_sum_mutually_orth _ _ BB90_X_rank BB90_X_ker_rank (by norm_num) BB90_X_ker_orth
lemma BB90_Z_ker_is_ker : BB90_Z_ker_mat.is_ker_for BB90_Z_mat := by
  apply Matrix.is_ker_for_of_rank_sum_mutually_orth _ _ BB90_Z_rank BB90_Z_ker_rank (by norm_num) BB90_Z_ker_orth
def BB90_css : CSS_pair 90 45 45 :=
  CSS_pair.of_matrices BB90_X_mat BB90_Z_mat BB90_XZ_orth
theorem BB90_dist_10 : 10 ≤ BB90_css.toBSM.distance (by norm_num) := by
  apply bitvec_sat_translation_correct BB90_css
      BB90_Z_ker_mat BB90_Z_ker_is_ker
      BB90_X_ker_mat BB90_X_ker_is_ker (by norm_num) _ _
  · rw [BB90_css, CSS_pair.of_matrices, ←BB90_X_correct, BB90_Z_ker_mat_correct]
    exact BB90_dist_z
  rw [BB90_css, CSS_pair.of_matrices, ←BB90_Z_correct, BB90_X_ker_mat_correct]
  exact BB90_dist_x
