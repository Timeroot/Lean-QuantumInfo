import LeanQEC.ComputerAlgebra.BitVecSAT
import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide
import LeanQEC.ComputerAlgebra.BitVecCorrectness
import LeanQEC.Stabilizer.BB
import LeanQEC.Stabilizer.BitVecSATToDist
set_option maxRecDepth 9999999
def BB70_A :=
  let l := 7
  let m := 5
  BB4_matrix l m (false, 2) (true, 2) (true, 3) (true, 4)
def BB70_B :=
  let l := 7
  let m := 5
  BB3_matrix l m (false, 1) (true, 1) (true, 3)
def BB70_X_mat := BB70_A.hstack_fin BB70_B
def BB70_Z_mat := BB70_B.transpose.hstack_fin BB70_A.transpose
def BB70_X : BitVec (35 * 70) := 0x200020080800842008000040101001084010000080240002108020000100480004210040000200900008420804000400010010841100000800020021082200001000800042104400002001000084208800004002000108410080008400200210022000010800400420044000021010000840088000042020001080110000084040002180201000108004004100440000210008008200880000420200010401100000840400020802200001080800041004020042100080002008800084200100004011000108404000008022000210808000010044000421010000020080400842001000040110001084002000080220002108080000100440004210100000200880008420200000401008010840020000802200021080040001004400042101000002008800084202000004011000108404
def BB70_Z : BitVec (35 * 70) := 0x808420002200800001010840004401000002021080008802000080042100011004000100084200402008000010108400044010000020210800088020000040421000110040001000842000220080002001084008040100000202108000880200000404210001100400000808420002200800020010840004401000040021080100802080004042000011004100008084000022008200010108000044010400400210000088020800800420002010061000080840000220042000101080000440084000202100000880108008004200001100210010008400040208420001000800004410840002001000008821080004002000011042100100004000022084200200008000804108400024010000080210800048020000100421000090040000200842002020080000401084004040100010
def BB70_X_ker : BitVec (38 * 70) := 0x800000002b61cc0a9900000000bc2b55014200000002d4358128840000000b06e7911608000000234802908c10000000944c33c3602000000283055caf004000000848861406008000002a28df92d00100000081490a102002000002a609b0774004000008026073a900080000254112520c00100000a0651671900020000214a9084ac00040000846c1ee32000080002a484e9ef800010000818828087000020002508c94c1000004000a1095852a000008002e40db5d340000100088690450100000200244b12c09c000004009d81136bb00000080290a10202800000100b8e811299000000202258d0982c0000004091a9681a200000008277301462400000010a40148463000000022539d342a000000004a16b1051300000000a16b5040b800000001a9ce6a6af000000001f0001f07c0000000003e007fff000000000007c1ff80000000000000f83ff
def BB70_Z_ker : BitVec (38 * 70) := 0x80000000022244185500000000044b0bee5200000000f0a9e8dc84000000021e5befb608000000044349df50100000002844b0bcf0200000005089617dc0400000035e1abee4008000000943f57208010000002c8891041002000000f508961780040000020a1eafd000080000046bc357dc0010000009287eae40002000001591122080004000005eae913d000080000f417dda0400010000208d8055000002000041250fd5c00004000082b2224400000800020bebddd80000100005e82fbb4000002000f41250f54000004002082b220500000080041056444800000100244185444000000200b0bee50880000004029e8dc9e1000000080541056440000000103482f2f77000000020448830a880000000409617dca1000000008153d1b93c000000013ca8d89370000000028693bea10000000007c00f83ff0000000000f83fff8000000000001f07fff
def BB70indrowsx : Fin 32 → Fin 35 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 30, 31, 32, 33]
lemma BB70StrictMono_indrowsx : StrictMono BB70indrowsx := by decide
def BB70indrowsz : Fin 32 → Fin 35 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 30, 31, 32, 33]
lemma BB70StrictMono_indrowsz : StrictMono BB70indrowsz := by decide
def BB70_X_submat : BitVec (32 * 70) := 0x80000401010010840100000802400021080200001004800042100400002009000084204400002000080084208800004002000108411000008004000210822000010008000421022000010800400420044000021010000840088000042020001080110000084040002180201000108004004100440000210008008200880000420200010401100000840400020802200001080800041004020042100080002008800084200100004011000108404000008022000210808000010044000421010000020080400842001000040110001084002000080220002108080000100440004210100000200880008420200000401008010840020000802200021080040001004400042101000002008800084202000004011000108404
set_option exponentiation.threshold 10000 in
lemma BB70_X_submat_correct : BB70_X_submat = flatten_matrix (BB70_X_mat.submatrix BB70indrowsx id) := by decide
def BB70_Z_submat : BitVec (32 * 70) := 0x10108400044010000020210800088020000800421000110040001000842004020080000080842000220080000101084000440100004002108000880200008004210020100400000404210001100400000808420002200800020010840004401000040021080100802080004042000011004100008084000022008200010108000044010400400210000088020800800420002010061000080840000220042000101080000440084000202100000880108008004200001100210010008400040208420001000800004410840002001000008821080004002000011042100100004000022084200200008000804108400024010000080210800048020000100421000090040000200842002020080000401084004040100010
set_option exponentiation.threshold 10000 in
lemma BB70_Z_submat_correct : BB70_Z_submat = flatten_matrix (BB70_Z_mat.submatrix BB70indrowsz id) := by decide
def BB70_X_ker_mat := BitVecMatrix BB70_X_ker
def BB70_Z_ker_mat := BitVecMatrix BB70_Z_ker
lemma BB70_X_ker_mat_correct : flatten_matrix BB70_X_ker_mat = BB70_X_ker := flatten_BitVecMatrix_id _
lemma BB70_Z_ker_mat_correct : flatten_matrix BB70_Z_ker_mat = BB70_Z_ker := flatten_BitVecMatrix_id _
set_option exponentiation.threshold 10000 in
lemma BB70_X_correct : BB70_X = flatten_matrix BB70_X_mat := by decide
set_option exponentiation.threshold 10000 in
lemma BB70_Z_correct : BB70_Z = flatten_matrix BB70_Z_mat := by decide
set_option maxHeartbeats 0 in
lemma BB70_X_rank : 32 ≤ BB70_X_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ BB70indrowsx BB70StrictMono_indrowsx
  rw [linear_indep_SAT_correct,  ←BB70_X_submat_correct, BB70_X_submat]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  sorry
set_option maxHeartbeats 0 in
lemma BB70_Z_rank : 32 ≤ BB70_Z_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ BB70indrowsz BB70StrictMono_indrowsx
  rw [linear_indep_SAT_correct,  ←BB70_Z_submat_correct, BB70_Z_submat]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  sorry
set_option maxHeartbeats 0 in
lemma BB70_X_ker_rank : 38 ≤ BB70_X_ker_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)
  rw [Matrix.submatrix_id_id]
  rw [linear_indep_SAT_correct, BB70_X_ker_mat_correct, BB70_X_ker]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  sorry
set_option maxHeartbeats 0 in
lemma BB70_Z_ker_rank : 38 ≤ BB70_Z_ker_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)
  rw [Matrix.submatrix_id_id]
  rw [linear_indep_SAT_correct, BB70_Z_ker_mat_correct, BB70_Z_ker]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  sorry
set_option exponentiation.threshold 10000
set_option maxHeartbeats 0
lemma BB70_XZ_orth : BB70_X_mat.mutually_orth_rows BB70_Z_mat := by
  rw [←mutually_orth_nat_correct, ←BB70_X_correct, ←BB70_Z_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option exponentiation.threshold 10000
set_option maxHeartbeats 0
lemma BB70_X_ker_orth : BB70_X_mat.mutually_orth_rows BB70_X_ker_mat := by
  rw [←mutually_orth_nat_correct, ←BB70_X_correct, BB70_X_ker_mat_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option exponentiation.threshold 10000
set_option maxHeartbeats 0
lemma BB70_Z_ker_orth : BB70_Z_mat.mutually_orth_rows BB70_Z_ker_mat := by
  rw [←mutually_orth_nat_correct, ←BB70_Z_correct, BB70_Z_ker_mat_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option maxHeartbeats 0 in
lemma BB70_dist_z : lt_dist_sat BB70_X BB70_Z_ker 8 7 := by
  rw [BB70_X, BB70_Z_ker]
  simp (maxSteps := 9999999) only [lt_dist_sat, Nat.reduceMul, loc_constraints, loc_constraints_aux, loc_constraints_ith,
  symmetry_constraints, symmetry_constraints_aux,  Nat.add_one_sub_one, Nat.lt_add_one, getElem!_pos, loc_constraints_ith_jth_aux,
  loc_constraints_ith_jth, one_mul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff,
  Nat.reduceLT, Nat.one_lt_ofNat, Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, dot_product_aux, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  sorry
set_option maxHeartbeats 0 in
lemma BB70_dist_x : lt_dist_sat BB70_Z BB70_X_ker 8 7 := by
  rw [BB70_Z, BB70_X_ker]
  simp (maxSteps := 9999999) only [lt_dist_sat, Nat.reduceMul, loc_constraints, loc_constraints_aux, loc_constraints_ith,
  symmetry_constraints, symmetry_constraints_aux,  Nat.add_one_sub_one, Nat.lt_add_one, getElem!_pos, loc_constraints_ith_jth_aux,
  loc_constraints_ith_jth, one_mul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff,
  Nat.reduceLT, Nat.one_lt_ofNat, Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, dot_product_aux, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  sorry
lemma BB70_X_ker_is_ker : BB70_X_ker_mat.is_ker_for BB70_X_mat := by
  apply Matrix.is_ker_for_of_rank_sum_mutually_orth _ _ BB70_X_rank BB70_X_ker_rank (by norm_num) BB70_X_ker_orth
lemma BB70_Z_ker_is_ker : BB70_Z_ker_mat.is_ker_for BB70_Z_mat := by
  apply Matrix.is_ker_for_of_rank_sum_mutually_orth _ _ BB70_Z_rank BB70_Z_ker_rank (by norm_num) BB70_Z_ker_orth
def BB70_css : CSS_pair 70 35 35 :=
  CSS_pair.of_matrices BB70_X_mat BB70_Z_mat BB70_XZ_orth
theorem BB70_dist_9 : 9 ≤ BB70_css.toBSM.distance (by norm_num) := by
  apply bitvec_sat_translation_correct BB70_css
      BB70_Z_ker_mat BB70_Z_ker_is_ker
      BB70_X_ker_mat BB70_X_ker_is_ker (by norm_num) _ _
  · rw [BB70_css, CSS_pair.of_matrices, ←BB70_X_correct, BB70_Z_ker_mat_correct]
    exact BB70_dist_z
  rw [BB70_css, CSS_pair.of_matrices, ←BB70_Z_correct, BB70_X_ker_mat_correct]
  exact BB70_dist_x
