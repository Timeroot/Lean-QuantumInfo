import numpy as np
from scipy.linalg import null_space
import sympy as sp
from sympy import Poly, symbols, Domain
from sympy import ZZ, QQ
from sympy.polys.domainmatrix import DomainMatrix
from sympy.polys.domains import GF
from math import ceil, log2

#BB code definitions
def cyclicshift(n, k):
    S = np.zeros((n, n), dtype = int)
    for i in range(n):
        S[i, (i+k) % n] = 1
    return S

def y(l, m, k):
    return np.kron(np.identity(l, dtype=int), cyclicshift(m, k))

def x(l, m, k):
    return np.kron(cyclicshift(l, k), np.identity(m, dtype=int))

def BB_x(A, B):
    return np.hstack((A, B))
    return np.hstack((A, B))

def BB_z(A, B):
    return(np.hstack((B.transpose(), A.transpose())))
    return np.hstack((B.transpose(), A.transpose()))

def ker_of(arr):
    dm = DomainMatrix(arr.tolist(), arr.shape, domain=GF(2))
    return np.array(dm.nullspace().to_Matrix())

def nparr_to_lean(arr):
    s = "!!["
    for row in arr:
        for elem in row:
            s = s + str(elem)+","
        s = s[:-1] + ";\n"
    s = s + "]"
    return s

def matrix_to_nat(matrix):
    # 1. Flatten the m x n matrix into a 1D array of m*n indices
    # 'C' order (row-major) is standard: [row0, row1, ...]
    flattened = np.array(matrix).astype(int)[::-1,::-1].flatten()
    
    # 2. Convert the bits to a binary string
    bit_string = ''.join(map(str, flattened))
    
    # 3. Convert binary string to a natural number (base 2)
    natural_number = int(bit_string, 2)
    
    return hex(natural_number), natural_number, bit_string

def greedy_independent_rows(matrix):
    """
    Greedily selects rows from top to bottom that are linearly 
    independent over F2.
    """
    num_rows, num_cols = matrix.shape
    
    selected_indices = []
    basis = [] # Stores the rows that form our current basis

    for i in range(num_rows):
        row = matrix[i].copy()
        
        # Reduce the current row using the basis already found
        for b in basis:
            # If the row has a 1 at the pivot position of the basis row, XOR them
            # This is the standard Gaussian elimination step over F2
            pivot = np.argmax(b == 1)
            if row[pivot] == 1:
                row = (row + b) % 2
        
        # If the row is not all zeros after reduction, it is independent
        if np.any(row):
            selected_indices.append(i)
            # Add to basis and keep basis in row-echelon form for efficiency
            basis.append(row)
            # Optional: Sort basis by leading coefficient (pivot) to speed up reduction
            basis.sort(key=lambda x: np.argmax(x == 1))

    return selected_indices, matrix[selected_indices]

def str_vec(vec):
    return "["+(", ".join(str(item) for item in vec))+"]"

def gen_BB_skeleton(filename, l, m, alist, blist, d):
    a1 = alist[0]
    a2 = alist[1]
    a3 = alist[2]
    b1 = blist[0]
    b2 = blist[1]
    b3 = blist[2]  
    s = l * m * 2
    A = a1[0](l, m, a1[1])+a2[0](l, m, a2[1])+a3[0](l, m, a3[1])
    if len(alist)== 4:
        a4 = alist[3]
        A += a4[0](l, m, a4[1])
    B = b1[0](l, m, b1[1])+b2[0](l, m, b2[1])+b3[0](l, m, b3[1])
    if len(blist)== 4:
        b4 = blist[3]
        B += b4[0](l, m, b4[1])
    A = A % 2
    B = B % 2
    X = np.hstack((A, B))
    Z = np.hstack((B.transpose(), A.transpose()))

    indrowsx = greedy_independent_rows(X)[0]
    indrowsz = greedy_independent_rows(Z)[0]
    
    hx_ind = matrix_to_nat(X[indrowsx])[0]
    hz_ind = matrix_to_nat(Z[indrowsz])[0]
    
    kerX = ker_of(X)
    kerZ = ker_of(Z)
    
    hkerx = matrix_to_nat(kerX)[0]
    hkerz = matrix_to_nat(kerZ)[0]
    
    r_x = len(indrowsx)
    r_z = len(indrowsz)
    n_k_x = kerX.shape[0]
    n_k_z = kerZ.shape[0]

    with open(filename, "w", encoding='utf-8') as f:
        f.write("import LeanQEC.ComputerAlgebra.BitVecSAT\n")
        f.write("import Lean.Elab.Tactic.BVDecide\n")
        f.write("import Std.Tactic.BVDecide\n")
        f.write("import LeanQEC.ComputerAlgebra.BitVecCorrectness\n")
        f.write("import LeanQEC.Stabilizer.BB\n")
        f.write("import LeanQEC.Stabilizer.BitVecSATToDist\n")
        f.write("set_option maxRecDepth 9999999\n")
        f.write(f"def BB{s}_A :=\n")
        f.write(f"  let l := {l}\n")
        f.write(f"  let m := {m}\n")
        def x_to_true(f):
            if f.__name__ == "x":
                return "true"
            else:
                return "false"
        if len(alist) == 3:
            f.write(f"  BB3_matrix l m ({x_to_true(a1[0])}, {a1[1]}) ({x_to_true(a2[0])}, {a2[1]}) ({x_to_true(a3[0])}, {a3[1]})\n")
        else:
            f.write(f"  BB4_matrix l m ({x_to_true(a1[0])}, {a1[1]}) ({x_to_true(a2[0])}, {a2[1]}) ({x_to_true(a3[0])}, {a3[1]}) ({x_to_true(a4[0])}, {a4[1]})\n")
        f.write(f"def BB{s}_B :=\n")
        f.write(f"  let l := {l}\n")
        f.write(f"  let m := {m}\n")
        if len(blist) == 3:
            f.write(f"  BB3_matrix l m ({x_to_true(b1[0])}, {b1[1]}) ({x_to_true(b2[0])}, {b2[1]}) ({x_to_true(b3[0])}, {b3[1]})\n")
        else:
            f.write(f"  BB4_matrix l m ({x_to_true(b1[0])}, {b1[1]}) ({x_to_true(b2[0])}, {b2[1]}) ({x_to_true(b3[0])}, {b3[1]}) ({x_to_true(b4[0])}, {b4[1]})\n")
        f.write(f"def BB{s}_X_mat := BB{s}_A.hstack_fin BB{s}_B\n")
        f.write(f"def BB{s}_Z_mat := BB{s}_B.transpose.hstack_fin BB{s}_A.transpose\n")
        f.write(f"def BB{s}_X : BitVec ({X.shape[0]} * {s}) := {matrix_to_nat(X)[0]}\n")
        f.write(f"def BB{s}_Z : BitVec ({Z.shape[0]} * {s}) := {matrix_to_nat(Z)[0]}\n")
        f.write(f"def BB{s}_X_ker : BitVec ({ker_of(X).shape[0]} * {s}) := {matrix_to_nat(ker_of(X))[0]}\n")
        f.write(f"def BB{s}_Z_ker : BitVec ({ker_of(Z).shape[0]} * {s}) := {matrix_to_nat(ker_of(Z))[0]}\n")
        f.write(f"def BB{s}indrowsx : Fin {r_x} → Fin {X.shape[0]} := !{str_vec(indrowsx)}\n")
        f.write(f"lemma BB{s}StrictMono_indrowsx : StrictMono BB{s}indrowsx := by decide\n")
        f.write(f"def BB{s}indrowsz : Fin {r_z} → Fin {Z.shape[0]} := !{str_vec(indrowsz)}\n")
        f.write(f"lemma BB{s}StrictMono_indrowsz : StrictMono BB{s}indrowsz := by decide\n")
        if(r_x != X.shape[0]):
            f.write(f"def BB{s}_X_submat : BitVec ({r_x} * {s}) := {matrix_to_nat(X[indrowsx])[0]}\n")
            f.write(f"set_option exponentiation.threshold 10000 in\n")
            f.write(f"lemma BB{s}_X_submat_correct : BB{s}_X_submat = flatten_matrix (BB{s}_X_mat.submatrix BB{s}indrowsx id) := by decide\n")
        if(r_z != Z.shape[0]):
            f.write(f"def BB{s}_Z_submat : BitVec ({r_z} * {s}) := {matrix_to_nat(Z[indrowsz])[0]}\n")
            f.write(f"set_option exponentiation.threshold 10000 in\n")
            f.write(f"lemma BB{s}_Z_submat_correct : BB{s}_Z_submat = flatten_matrix (BB{s}_Z_mat.submatrix BB{s}indrowsz id) := by decide\n")
        f.write(f"def BB{s}_X_ker_mat := BitVecMatrix BB{s}_X_ker\n")
        f.write(f"def BB{s}_Z_ker_mat := BitVecMatrix BB{s}_Z_ker\n")
        f.write(f"lemma BB{s}_X_ker_mat_correct : flatten_matrix BB{s}_X_ker_mat = BB{s}_X_ker := flatten_BitVecMatrix_id _\n")
        f.write(f"lemma BB{s}_Z_ker_mat_correct : flatten_matrix BB{s}_Z_ker_mat = BB{s}_Z_ker := flatten_BitVecMatrix_id _\n")
        f.write(f"set_option exponentiation.threshold 10000 in\n")
        f.write(f"lemma BB{s}_X_correct : BB{s}_X = flatten_matrix BB{s}_X_mat := by decide\n")
        f.write(f"set_option exponentiation.threshold 10000 in\n")
        f.write(f"lemma BB{s}_Z_correct : BB{s}_Z = flatten_matrix BB{s}_Z_mat := by decide\n")
        f.write(f"set_option maxHeartbeats 0 in\n")
        f.write(f"lemma BB{s}_X_rank : {r_x} ≤ BB{s}_X_mat.rank := by\n")
        f.write(f"  apply Matrix.rank_le_of_submatrix_independent _ BB{s}indrowsx BB{s}StrictMono_indrowsx\n")
        f.write(f"  rw [linear_indep_SAT_correct,  ←BB{s}_X_submat_correct, BB{s}_X_submat]\n")
        f.write(f"  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,\n")
        f.write(f"      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,\n")
        f.write(f"      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,\n")
        f.write(f"      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,\n")
        f.write(f"      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,\n")
        f.write(f"      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,\n")
        f.write(f"      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq, Nat.reduceSucc]\n")
        f.write(f"  bv_decide\n")
        f.write(f"set_option maxHeartbeats 0 in\n")
        f.write(f"lemma BB{s}_Z_rank : {r_z} ≤ BB{s}_Z_mat.rank := by\n")
        f.write(f"  apply Matrix.rank_le_of_submatrix_independent _ BB{s}indrowsz BB{s}StrictMono_indrowsx\n")
        f.write(f"  rw [linear_indep_SAT_correct,  ←BB{s}_Z_submat_correct, BB{s}_Z_submat]\n")
        f.write(f"  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,\n")
        f.write(f"      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,\n")
        f.write(f"      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,\n")
        f.write(f"      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,\n")
        f.write(f"      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,\n")
        f.write(f"      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,\n")
        f.write(f"      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq, Nat.reduceSucc]\n")
        f.write(f"  bv_decide\n")
        f.write(f"set_option maxHeartbeats 0 in\n")
        f.write(f"lemma BB{s}_X_ker_rank : {kerX.shape[0]} ≤ BB{s}_X_ker_mat.rank := by\n")
        f.write(f"  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)\n")
        f.write(f"  rw [Matrix.submatrix_id_id]\n")
        f.write(f"  rw [linear_indep_SAT_correct, BB{s}_X_ker_mat_correct, BB{s}_X_ker]\n")
        f.write(f"  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,\n")
        f.write(f"      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,\n")
        f.write(f"      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,\n")
        f.write(f"      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,\n")
        f.write(f"      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,\n")
        f.write(f"      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,\n")
        f.write(f"      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq, Nat.reduceSucc]\n")
        f.write(f"  bv_decide\n")
        f.write(f"set_option maxHeartbeats 0 in\n")
        f.write(f"lemma BB{s}_Z_ker_rank : {kerZ.shape[0]} ≤ BB{s}_Z_ker_mat.rank := by\n")
        f.write(f"  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)\n")
        f.write(f"  rw [Matrix.submatrix_id_id]\n")
        f.write(f"  rw [linear_indep_SAT_correct, BB{s}_Z_ker_mat_correct, BB{s}_Z_ker]\n")
        f.write(f"  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,\n")
        f.write(f"      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,\n")
        f.write(f"      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,\n")
        f.write(f"      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,\n")
        f.write(f"      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,\n")
        f.write(f"      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,\n")
        f.write(f"      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq, Nat.reduceSucc]\n")
        f.write(f"  bv_decide\n")
        f.write(f"set_option exponentiation.threshold 10000\n")
        f.write(f"set_option maxHeartbeats 0\n")
        f.write(f"lemma BB{s}_XZ_orth : BB{s}_X_mat.mutually_orth_rows BB{s}_Z_mat := by\n")
        f.write(f"  rw [←mutually_orth_nat_correct, ←BB{s}_X_correct, ←BB{s}_Z_correct]\n")
        f.write(f"  unfold bitvec_mutually_orth_nat\n")
        f.write(f"  native_decide\n")
        f.write(f"set_option exponentiation.threshold 10000\n")
        f.write(f"set_option maxHeartbeats 0\n")
        f.write(f"lemma BB{s}_X_ker_orth : BB{s}_X_mat.mutually_orth_rows BB{s}_X_ker_mat := by\n")
        f.write(f"  rw [←mutually_orth_nat_correct, ←BB{s}_X_correct, BB{s}_X_ker_mat_correct]\n")
        f.write(f"  unfold bitvec_mutually_orth_nat\n")
        f.write(f"  native_decide\n")
        f.write(f"set_option exponentiation.threshold 10000\n")
        f.write(f"set_option maxHeartbeats 0\n")
        f.write(f"lemma BB{s}_Z_ker_orth : BB{s}_Z_mat.mutually_orth_rows BB{s}_Z_ker_mat := by\n")
        f.write(f"  rw [←mutually_orth_nat_correct, ←BB{s}_Z_correct, BB{s}_Z_ker_mat_correct]\n")
        f.write(f"  unfold bitvec_mutually_orth_nat\n")
        f.write(f"  native_decide\n")
        f.write(f"set_option maxHeartbeats 0 in\n")
        f.write(f"lemma BB{s}_dist_z : lt_dist_sat BB{s}_X BB{s}_Z_ker {d-1} {int(ceil(log2(s)))} := by\n")
        f.write(f"  rw [BB{s}_X, BB{s}_Z_ker]\n")
        f.write(f"  simp (maxSteps := 9999999) only [lt_dist_sat, Nat.reduceMul, loc_constraints, loc_constraints_aux, loc_constraints_ith,\n")
        f.write(f"  symmetry_constraints, symmetry_constraints_aux,")
        f.write(f"  Nat.add_one_sub_one, Nat.lt_add_one, getElem!_pos, loc_constraints_ith_jth_aux,\n")
        f.write(f"  loc_constraints_ith_jth, one_mul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff,\n")
        f.write(f"  Nat.reduceLT, Nat.one_lt_ofNat, Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parity_constraints,\n")
        f.write(f"  parity_constraints_aux, BitVec.dot_product, dot_product_aux, BitVec.row,\n")
        f.write(f"  Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq, decide_eq_true_eq, rowspace_constraints,\n")
        f.write(f"  rowspace_constraints_aux, not_and, and_imp]\n")
        f.write(f"  bv_decide (timeout := 9999) (maxSteps := 9999999)\n")
        f.write(f"set_option maxHeartbeats 0 in\n")
        f.write(f"lemma BB{s}_dist_x : lt_dist_sat BB{s}_Z BB{s}_X_ker {d-1} {int(ceil(log2(s)))} := by\n")
        f.write(f"  rw [BB{s}_Z, BB{s}_X_ker]\n")
        f.write(f"  simp (maxSteps := 9999999) only [lt_dist_sat, Nat.reduceMul, loc_constraints, loc_constraints_aux, loc_constraints_ith,\n")
        f.write(f"  symmetry_constraints, symmetry_constraints_aux,")
        f.write(f"  Nat.add_one_sub_one, Nat.lt_add_one, getElem!_pos, loc_constraints_ith_jth_aux,\n")
        f.write(f"  loc_constraints_ith_jth, one_mul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff,\n")
        f.write(f"  Nat.reduceLT, Nat.one_lt_ofNat, Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parity_constraints,\n")
        f.write(f"  parity_constraints_aux, BitVec.dot_product, dot_product_aux, BitVec.row,\n")
        f.write(f"  Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq, decide_eq_true_eq, rowspace_constraints,\n")
        f.write(f"  rowspace_constraints_aux, not_and, and_imp]\n")
        f.write(f"  bv_decide (timeout := 9999) (maxSteps := 9999999)\n")
        f.write(f"lemma BB{s}_X_ker_is_ker : BB{s}_X_ker_mat.is_ker_for BB{s}_X_mat := by\n")
        f.write(f"  apply Matrix.is_ker_for_of_rank_sum_mutually_orth _ _ BB{s}_X_rank BB{s}_X_ker_rank (by norm_num) BB{s}_X_ker_orth\n")
        f.write(f"lemma BB{s}_Z_ker_is_ker : BB{s}_Z_ker_mat.is_ker_for BB{s}_Z_mat := by\n")
        f.write(f"  apply Matrix.is_ker_for_of_rank_sum_mutually_orth _ _ BB{s}_Z_rank BB{s}_Z_ker_rank (by norm_num) BB{s}_Z_ker_orth\n")
        f.write(f"def BB{s}_css : CSS_pair {s} {int(s/2)} {int(s/2)} :=\n")
        f.write(f"  CSS_pair.of_matrices BB{s}_X_mat BB{s}_Z_mat BB{s}_XZ_orth\n")
        f.write(f"theorem BB{s}_dist_{d} : {d} ≤ BB{s}_css.toBSM.distance (by norm_num) := by\n")
        f.write(f"  apply bitvec_sat_translation_correct BB{s}_css\n")
        f.write(f"      BB{s}_Z_ker_mat BB{s}_Z_ker_is_ker\n")
        f.write(f"      BB{s}_X_ker_mat BB{s}_X_ker_is_ker (by norm_num) _ _\n")
        f.write(f"  · rw [BB{s}_css, CSS_pair.of_matrices, ←BB{s}_X_correct, BB{s}_Z_ker_mat_correct]\n")
        f.write(f"    exact BB{s}_dist_z\n")
        f.write(f"  rw [BB{s}_css, CSS_pair.of_matrices, ←BB{s}_Z_correct, BB{s}_X_ker_mat_correct]\n")
        f.write(f"  exact BB{s}_dist_x\n")

#gen_BB_skeleton("LeanQEC/Stabilizer/Examples/BB/BB18.lean", 3, 3, ((x, 0), (x, 1), (y, 1)), ((x, 0), (x, 2), (y, 2)), 4)
#gen_BB_skeleton("LeanQEC/Stabilizer/Examples/BB/BB54.lean", 3, 9, ((x, 0), (y, 2), (y, 4)), ((x, 1), (x, 2), (y, 3)), 6)
#gen_BB_skeleton("LeanQEC/Stabilizer/Examples/BB/BB72.lean", 6, 6, ((x, 3), (y, 1), (y, 2)), ((x, 1), (x, 2), (y, 3)), 6)
#gen_BB_skeleton("LeanQEC/Stabilizer/Examples/BB/BB90.lean", 15, 3, ((x, 9), (y, 1), (y, 2)), ((y, 0), (x, 2), (x, 7)), 10)
#gen_BB_skeleton("LeanQEC/Stabilizer/Examples/BB/BB108.lean", 9, 6, ((x, 3), (y, 1), (y, 2)), ((y, 3), (x, 1), (x, 2)), 10)
#gen_BB_skeleton("LeanQEC/Stabilizer/Examples/BB/BB70.lean", 7, 5, ((y, 2), (x, 2), (x, 3), (x, 4)), ((y, 1), (x, 1), (x, 3)), 9)
#gen_BB_skeleton("LeanQEC/Stabilizer/Examples/BB/GB54.lean", 27, 1, ((x, 8), (x, 13), (x, 15), (x, 16)), ((x, 7), (x, 8), (x, 10), (x, 15)), 10)
#gen_BB_skeleton("LeanQEC/Stabilizer/Examples/BB/BB144.lean", 12, 6, ((x, 3), (y, 1), (y, 2)), ((y, 3), (x, 1), (x, 2)), 12)
gen_BB_skeleton("LeanQEC/Stabilizer/Examples/BB/BB162.lean", 3, 27, ((x, 0), (y, 10), (y, 14)), ((y, 12), (x, 1), (x, 2)), 14)
gen_BB_skeleton("LeanQEC/Stabilizer/Examples/BB/BB180.lean", 6, 15, ((x, 3), (y, 1), (y, 2)), ((y, 6), (x, 4), (x, 5)), 16)
gen_BB_skeleton("LeanQEC/Stabilizer/Examples/BB/BB288.lean", 12, 12, ((x, 3), (y, 2), (y, 7)), ((y, 3), (x, 1), (x, 2)), 18)

