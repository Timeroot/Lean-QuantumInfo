/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.LogExp
import QuantumInfo.ForMathlib.HermitianMat.Sqrt

variable {d d₂ 𝕜 : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]
variable [RCLike 𝕜]
variable {A B : HermitianMat d 𝕜} {x q r : ℝ}

/-! # Matrix powers with real exponents

-/

noncomputable section
namespace HermitianMat

/-- Matrix power of a positive semidefinite matrix, as given by the elementwise
  real power of the diagonal in a diagonalized form.

  Note that this has the usual `Real.rpow` caveats, such as 0 to the power -1 giving 0. -/
def rpow (A : HermitianMat d 𝕜) (r : ℝ) : HermitianMat d 𝕜 :=
  A.cfc (Real.rpow · r)

instance instRPow : Pow (HermitianMat d 𝕜) ℝ :=
  ⟨rpow⟩

theorem rpow_conj_unitary (A : HermitianMat d 𝕜) (U : Matrix.unitaryGroup d 𝕜) (r : ℝ) :
    (HermitianMat.conj U.val A) ^ r = HermitianMat.conj U.val (A ^ r) := by
  exact A.cfc_conj_unitary (· ^ r) U

theorem pow_eq_rpow : A ^ r = A.rpow r :=
  rfl

theorem rpow_eq_cfc : A ^ r = A.cfc (· ^ r) :=
  rfl

theorem diagonal_pow (f : d → ℝ) :
    (diagonal 𝕜 f) ^ r = diagonal 𝕜 (fun i ↦ (f i) ^ r) := by
  simp [rpow_eq_cfc]
  rfl

@[fun_prop]
theorem rpow_const_continuous {r : ℝ} (hr : 0 ≤ r) : Continuous (fun A : HermitianMat d ℂ ↦ A ^ r) := by
  exact HermitianMat.cfc_continuous (Real.continuous_rpow_const hr)

@[fun_prop]
theorem const_rpow_continuous [NonSingular A] : Continuous (fun r : ℝ ↦ A ^ r) := by
  rw [← continuousOn_univ]
  apply continuousOn_cfc_fun_nonsingular
  simp only [Real.rpow_eq_pow]
  fun_prop (disch := assumption)

/--
For a fixed Hermitian matrix A, the function x ↦ A^x is continuous for x > 0.
-/
@[fun_prop]
theorem continuousOn_rpow_pos (A : HermitianMat d ℂ) : ContinuousOn (fun x : ℝ ↦ A ^ x) (Set.Ioi 0) := by
  apply A.continuousOn_cfc_fun (hA := subset_rfl)
  intro i _ x hx
  exact (Real.continuousAt_const_rpow' hx.ne').continuousWithinAt

/--
For a fixed Hermitian matrix A, the function x ↦ A^x is continuous for x < 0.
-/
@[fun_prop]
theorem continuousOn_rpow_neg (A : HermitianMat d ℂ) : ContinuousOn (fun x : ℝ ↦ A ^ x) (Set.Iio 0) := by
  apply A.continuousOn_cfc_fun (hA := subset_rfl)
  intro i _ x hx
  exact (Real.continuousAt_const_rpow' hx.ne).continuousWithinAt

@[simp]
theorem rpow_one : A ^ (1 : ℝ) = A := by
  simp [rpow_eq_cfc]

/--
Functional calculus of Real.sqrt is equal to functional calculus of x^(1/2).
-/
lemma sqrt_eq_cfc_rpow_half (A : HermitianMat d 𝕜)  :
    A.sqrt = A.cfc (fun x ↦ x ^ (1/2 : ℝ)) := by
  rw [sqrt, cfc_eq_cfc_iff_eqOn]
  intro
  simp [Real.sqrt_eq_rpow]

@[simp]
theorem one_rpow : (1 : HermitianMat d 𝕜) ^ r = 1 := by
  rcases isEmpty_or_nonempty d
  · apply Subsingleton.allEq
  · nth_rw 2 [← HermitianMat.cfc_id (1 : HermitianMat d 𝕜)]
    rw [rpow_eq_cfc]
    gcongr
    simp

/-- Keeps in line with our simp-normal form for moving reindex outwards. -/
@[simp]
theorem reindex_rpow (e : d ≃ d₂) :
    A.reindex e ^ r = (A ^ r).reindex e := by
  apply A.cfc_reindex

theorem mat_rpow_add (hA : 0 ≤ A) {p q : ℝ} (hpq : p + q ≠ 0) :
    (A ^ (p + q)).mat = (A ^ p).mat * (A ^ q).mat := by
  simp only [rpow_eq_cfc, ← mat_cfc_mul, ← HermitianMat.ext_iff]
  exact cfc_congr_of_nonneg hA (fun i hi ↦ Real.rpow_add' hi hpq)

theorem rpow_mul (hA : 0 ≤ A) {p q : ℝ} : A ^ (p * q) = (A ^ p) ^ q := by
  simp only [rpow_eq_cfc, ← cfc_comp]
  exact cfc_congr_of_nonneg hA (fun i hi ↦ Real.rpow_mul hi p q)

theorem conj_rpow (hA : 0 ≤ A) (hq : q ≠ 0) (hqr : r + 2 * q ≠ 0) :
    (A ^ r).conj (A ^ q) = A ^ (r + 2 * q) := by
  simp only [rpow_eq_cfc, cfc_conj]
  refine cfc_congr_of_nonneg hA (fun i hi ↦ ?_)
  rw [pow_two, Real.rpow_add' hi hqr, two_mul, Real.rpow_add' hi (by simpa)]
  rfl

theorem pow_half_mul (hA : 0 ≤ A) :
    (A ^ (1/2 : ℝ)).mat * (A ^ (1/2 : ℝ)).mat = A := by
  rw [← mat_rpow_add hA]
  · norm_num
  · norm_num

theorem rpow_pos {A : HermitianMat d 𝕜} (hA : 0 < A) {p : ℝ} : 0 < A ^ p := by
  convert cfc_pos_of_pos hA _ _
  · exact fun i hi => Real.rpow_pos_of_pos hi _
  · rcases eq_or_ne p 0 with h | h <;> simp [h]

theorem rpow_nonneg (hA : 0 ≤ A) {p : ℝ} : 0 ≤ A ^ p := by
  apply cfc_nonneg_of_nonneg hA
  exact fun i hi => Real.rpow_nonneg hi p

open ComplexOrder in
theorem inv_eq_rpow_neg_one (hA : A.mat.PosDef) : A⁻¹ = A ^ (-1 : ℝ) := by
  have := nonSingular_of_posDef hA
  rw [← cfc_inv, rpow_eq_cfc]
  simp_rw [Real.rpow_neg_one]

open ComplexOrder in
theorem sandwich_self (hB : B.mat.PosDef) :
    (B.conj (B ^ (-1/2 : ℝ)).mat) = 1 := by
  have hB_inv_sqrt : (B ^ (-1 / 2 : ℝ)).mat * (B ^ (-1 / 2 : ℝ)).mat = (B ^ (-1 : ℝ)).mat := by
    rw [ ← mat_rpow_add ] <;> norm_num
    rw [zero_le_iff]
    exact hB.posSemidef
  have hB_inv : (B ^ (-1 : ℝ)).mat = B.mat⁻¹ := by
    rw [← inv_eq_rpow_neg_one hB, mat_inv]
  rw [ hB_inv ] at hB_inv_sqrt;
  ext1
  simp [mul_assoc];
  rw [ ← Matrix.mul_assoc, Matrix.mul_eq_one_comm.mp ];
  rw [ ← Matrix.mul_assoc, hB_inv_sqrt, Matrix.nonsing_inv_mul _ ];
  exact isUnit_iff_ne_zero.mpr hB.det_pos.ne'

open ComplexOrder in
lemma rpow_inv_eq_neg_rpow (hA : A.mat.PosDef) (p : ℝ) : (A ^ p)⁻¹ = A ^ (-p) := by
  --TODO cleanup
  ext i j;
  have h_inv : (A ^ p).mat * (A ^ (-p)).mat = 1 := by
    have h_inv : (A ^ p).mat * (A ^ (-p)).mat = 1 := by
      have h_pow : (A ^ p).mat = A.cfc (fun x => x ^ p) := by
        exact rfl
      have h_pow_neg : (A ^ (-p)).mat = A.cfc (fun x => x ^ (-p)) := by
        exact rfl
      have h_inv : (A ^ p).mat * (A ^ (-p)).mat = A.cfc (fun x => x ^ p * x ^ (-p)) := by
        rw [ h_pow, h_pow_neg, ← mat_cfc_mul ];
        rfl;
      have h_inv : (A ^ p).mat * (A ^ (-p)).mat = A.cfc (fun x => 1) := by
        rw [ h_inv ];
        refine' congr_arg _ ( cfc_congr_of_posDef hA _ );
        exact fun x hx => by simp [ ← Real.rpow_add hx ] ;
      rw [ h_inv, cfc_const ] ; norm_num;
    exact h_inv;
  -- By definition of matrix inverse, if $(A^p) * (A^{-p}) = 1$, then $(A^{-p})$ is the inverse of $(A^p)$.
  have h_inv_def : (A ^ p).mat⁻¹ = (A ^ (-p)).mat := by
    exact Matrix.inv_eq_right_inv h_inv;
  convert congr_fun ( congr_fun h_inv_def i ) j using 1

open ComplexOrder in
lemma sandwich_le_one (hB : B.mat.PosDef) (h : A ≤ B) :
    (A.conj (B ^ (-1/2 : ℝ)).mat) ≤ 1 := by
  convert ← conj_mono h using 1
  exact sandwich_self hB

open ComplexOrder in
lemma rpow_neg_mul_rpow_self (hA : A.mat.PosDef) (p : ℝ) :
    (A ^ (-p)).mat * (A ^ p).mat = 1 := by
  have := rpow_inv_eq_neg_rpow hA p;
  rw [ ← this ];
  -- Since $A$ is positive definite, $A^p$ is also positive definite.
  have h_pos_def : (A ^ p).mat.PosDef := by
    have h_pos_def : ∀ p : ℝ, A.mat.PosDef → (A ^ p).mat.PosDef := by
      intro p hA_pos_def
      have h_eigenvalues_pos : ∀ i, 0 < (A.H.eigenvalues i) ^ p := by
        exact fun i => Real.rpow_pos_of_pos ( by exact Matrix.PosDef.eigenvalues_pos hA i ) _;
      have h_eigenvalues_pos : (A ^ p).mat.PosDef ↔ ∀ i, 0 < (A ^ p).H.eigenvalues i := by
        exact Matrix.IsHermitian.posDef_iff_eigenvalues_pos (H (A ^ p));
      have h_eigenvalues_pos : ∃ e : d ≃ d, (A ^ p).H.eigenvalues = fun i => (A.H.eigenvalues (e i)) ^ p := by
        exact Matrix.IsHermitian.cfc_eigenvalues (H A) fun x => x.rpow p;
      aesop;
    exact h_pos_def p hA;
  convert Matrix.nonsing_inv_mul _ _;
  exact isUnit_iff_ne_zero.mpr h_pos_def.det_pos.ne'

open ComplexOrder in
lemma isUnit_rpow_toMat (hA : A.mat.PosDef) (p : ℝ) : IsUnit (A ^ p).mat := by
  have hA_inv : IsUnit (A ^ (-p)).mat := by
    have hA_inv : (A ^ (-p)).mat * (A ^ p).mat = 1 := by
      exact rpow_neg_mul_rpow_self hA p
    exact Matrix.isUnit_of_right_inverse hA_inv;
  -- Since $(A^{-p}) (A^p) = 1$, we have that $(A^p)$ is the inverse of $(A^{-p})$.
  have hA_inv : (A ^ p).mat = (A ^ (-p)).mat⁻¹ := by
    have hA_inv : (A ^ (-p)).mat * (A ^ p).mat = 1 := by
      exact rpow_neg_mul_rpow_self hA p;
    exact Eq.symm (Matrix.inv_eq_right_inv hA_inv);
  aesop

open ComplexOrder in
lemma sandwich_inv (hB : B.mat.PosDef) :
    (A.conj (B ^ (-1/2 : ℝ)).mat)⁻¹ = A⁻¹.conj (B ^ (1/2 : ℝ)).mat := by
  have h_inv : (B ^ (-1 / 2 : ℝ)).mat⁻¹ = (B ^ (1 / 2 : ℝ)).mat := by
    apply Matrix.inv_eq_right_inv
    rw [← rpow_neg_mul_rpow_self hB (1 / 2), neg_div 2 1]
  simp [inv_conj (isUnit_rpow_toMat hB _), h_inv]

theorem ker_rpow_eq_of_nonneg {A : HermitianMat d ℂ} (hA : 0 ≤ A) (hp : r ≠ 0):
    (A ^ r).ker = A.ker := by
  apply ker_cfc_eq_ker_nonneg hA
  grind [Real.rpow_eq_zero_iff_of_nonneg, Real.rpow_eq_pow]

theorem ker_rpow_le_of_nonneg {A : HermitianMat d ℂ} (hA : 0 ≤ A) :
    (A ^ r).ker ≤ A.ker := by
  apply ker_cfc_le_ker_nonneg hA
  grind [Real.rpow_eq_zero_iff_of_nonneg, Real.rpow_eq_pow]
