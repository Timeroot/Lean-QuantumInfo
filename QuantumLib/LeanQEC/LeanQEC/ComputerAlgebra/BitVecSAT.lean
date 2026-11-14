import Mathlib.Data.BitVec
import LeanQEC.LinearAlgebra.RowspaceKernel
import Init.Data.BitVec.Basic

--locs : BitVec (k * nlog), where nlog is ceiling of log_2 n
@[simp]
def loc_constraints_ith_jth
  {nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (i j : ℕ) :=
  ((locs.extractLsb' (j * nlog) nlog) = i)
  --obtain jth entry of locs, which is a BitVec of length nlog
  --and test it against i, which is a natural number

@[simp]
def loc_constraints_ith_jth_aux
  {nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (i j : ℕ) :=
  match j with
  | 0 => loc_constraints_ith_jth locs i 0
  | j' + 1 => loc_constraints_ith_jth locs i j ∨
              loc_constraints_ith_jth_aux locs i j'

@[simp]
def loc_constraints_ith
  {n nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (errs : BitVec n)
  (i : ℕ) :=
  errs[i]! = loc_constraints_ith_jth_aux locs i (k-1)

@[simp]
def loc_constraints_aux
  {n nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (errs : BitVec n)
  (c : ℕ) :=
  match c with
  | 0 => loc_constraints_ith locs errs 0
  | c' + 1 =>
    loc_constraints_ith locs errs c ∧
    loc_constraints_aux locs errs c'

def loc_constraints
  {n nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (errs : BitVec n) :=
  loc_constraints_aux locs errs (n-1)

def symmetry_constraints_aux
  {nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (c : ℕ) (prev : BitVec nlog) : Bool :=
  let val := locs.extractLsb' (c * nlog) nlog
  match c with
  | 0 => val ≤ prev
  | c' + 1 => (val ≤ prev) && (symmetry_constraints_aux locs c' val)

def symmetry_constraints
  {nlog k : ℕ}
  (locs : BitVec (k * nlog)) :=
  symmetry_constraints_aux locs (k - 1) (BitVec.allOnes nlog)

def dot_product_aux {n : ℕ} [NeZero n] (x y : BitVec n) (c : ℕ) (hc : c < n) : Bool :=
  let b := x[c] && y[c]
  match c with
  | 0 => b
  | c' + 1 => b ^^ dot_product_aux x y c' (lt_of_le_of_lt (Nat.le_succ _) hc)

def BitVec.dot_product {n : ℕ} [NeZero n] (x y : BitVec n) := dot_product_aux x y (n-1) (Nat.sub_one_lt (NeZero.ne _))

--updated definition to account for r unknown at runtime
def BitVec.row {n k : ℕ} (M : BitVec (k * n)) (r : ℕ) : BitVec n := (M >>> (r * n)).extractLsb' 0 n

def BitVec.row_bv {n k klog : ℕ} (M : BitVec (k * n)) (r : BitVec klog) : BitVec n := (M >>> ((r.zeroExtend (k * n) * (n : BitVec (k * n))))).extractLsb' 0 n



@[simp]
def parity_constraints_aux {stabdim n : ℕ} [NeZero n] (stabs : BitVec (stabdim * n)) (errs : BitVec n) (r : ℕ) :=
  match r with
  | 0 => !(errs.dot_product (stabs.row 0))
  | r' + 1 => !(errs.dot_product (stabs.row r)) ∧ parity_constraints_aux stabs errs r'


def parity_constraints {stabdim n : ℕ} [NeZero n] (stabs : BitVec (stabdim * n)) (errs : BitVec n) :=
  parity_constraints_aux stabs errs (stabdim-1)

@[simp]
def rowspace_constraints_aux
  {kerdim n : ℕ}
  [NeZero n]
  (ker : BitVec (kerdim * n))
  (errs : BitVec n) (r : ℕ) :=
  match r with
  | 0 => (errs.dot_product (ker.row 0))
  | r' + 1 => (errs.dot_product (ker.row r)) ∨
      rowspace_constraints_aux ker errs r'

def rowspace_constraints
  {kerdim n : ℕ}
  [NeZero n]
  (ker : BitVec (kerdim * n))
  (errs : BitVec n) :=
  rowspace_constraints_aux ker errs (kerdim - 1)

def lt_dist_sat
  {n stabdim kerdim : ℕ}
  [NeZero n]
  (stabs : BitVec (stabdim * n))
  (ker : BitVec (kerdim * n))
  (k nlog : ℕ) : Prop :=
  ∀ (locs : (BitVec (k * nlog))) (errs : BitVec n),
  ¬ (loc_constraints locs errs ∧ symmetry_constraints locs ∧ parity_constraints stabs errs ∧ rowspace_constraints ker errs)


def bitvec_mutually_orth
  {n k₁ k₂ : ℕ}
  [NeZero n]
  (M₁ : BitVec (k₁ * n))
  (M₂ : BitVec (k₂ * n)) : Prop :=
  ∀ (i : BitVec (Nat.clog 2 k₁)) (j : BitVec (Nat.clog 2 k₂)), !((M₁.row_bv i).dot_product (M₂.row_bv j) && i < k₁ && j < k₂)

def mutually_orth_row_sat_aux
  {n k₁ k₂ : ℕ}
  [NeZero n]
  (M₁ : BitVec (k₁ * n))
  (M₂ : BitVec (k₂ * n))
  (i j : ℕ) : Bool :=
  match j with
  | 0 => !((M₁.row i).dot_product (M₂.row 0))
  | j' + 1 => !((M₁.row i).dot_product (M₂.row j)) && mutually_orth_row_sat_aux M₁ M₂ i j'

def mutually_orth_sat_aux
  {n k₁ k₂ : ℕ}
  [NeZero n]
  [NeZero k₂]
  (M₁ : BitVec (k₁ * n))
  (M₂ : BitVec (k₂ * n))
  (i : ℕ) : Bool :=
  match i with
  | 0 => mutually_orth_row_sat_aux M₁ M₂ 0 (k₂ - 1)
  | i' + 1 => mutually_orth_row_sat_aux M₁ M₂ i (k₂ - 1) && mutually_orth_sat_aux M₁ M₂ i'

def bitvec_mutually_orth_nat
  {n k₁ k₂ : ℕ}
  [NeZero n]
  [NeZero k₁]
  [NeZero k₂]
  (M₁ : BitVec (k₁ * n))
  (M₂ : BitVec (k₂ * n)) : Prop :=
  mutually_orth_sat_aux M₁ M₂ (k₁ - 1)

@[simp]
def nonzero_aux {r : ℕ} (coeffs : BitVec r) (i : ℕ) :=
  match i with
  | 0 => coeffs[0]!
  | i₀ + 1 => (coeffs[i]!) ∨ nonzero_aux coeffs i₀

@[simp]
def nonzero {r : ℕ} (coeffs : BitVec r) := nonzero_aux coeffs (r-1)

@[simp]
def dot_col_aux {n r : ℕ} (coeffs : BitVec r) (mat : BitVec (r * n)) (c : ℕ) (i : ℕ) :=
  let k := i * n + c
  match i with
  | 0 => coeffs[i]! && mat[k]!
  | i₀ + 1 => (coeffs[i]! && mat[k]!) ^^ dot_col_aux coeffs mat c i₀

@[simp]
def dot_col_zero {n r : ℕ} (coeffs : BitVec r) (mat : BitVec (r * n)) (c : ℕ) :=
  let dot := dot_col_aux coeffs mat c (r-1)
  !dot

@[simp]
def all_dot_zero_aux {r n : ℕ} (coeffs : BitVec r) (mat : BitVec (r * n)) (c : ℕ) :=
  match c with
  | 0 => (dot_col_zero coeffs mat 0)
  | c₀ + 1 => dot_col_zero coeffs mat c && all_dot_zero_aux coeffs mat c₀

@[simp]
def all_dot_zero {r n : ℕ} (coeffs : BitVec r) (mat : BitVec (r * n)) := all_dot_zero_aux coeffs mat (n-1)

def linear_indep_SAT {r n : ℕ} (mat : BitVec (r * n)) : Prop := ∀ coeffs, !(nonzero coeffs && all_dot_zero coeffs mat)


def inds_strict_mono_aux {k r : ℕ} (inds : Fin r → Fin k) (i : Fin r) (prev : ℕ) : Bool :=
  let b := (inds i).1.blt prev
  match i with
  | ⟨0, _⟩ => b
  | ⟨i' + 1, h⟩ => b && (inds_strict_mono_aux inds ⟨i', (Nat.lt_succ_self _).trans h⟩ (inds i).1)

def inds_strict_mono {k r : ℕ} [NeZero r] (inds : Fin r → Fin k) : Prop := inds_strict_mono_aux inds ⟨r-1, Nat.sub_one_lt (NeZero.ne _)⟩ k
