/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy.Entropy
public import QIT.Information.Entropy.EntropyTensorPower
public import QIT.Information.Renyi.Renyi
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Data.Real.Basic

/-!
# Typical-subspace projector and Schumacher compression

Definitions for the quantum typical subspace and Schumacher compression rate.

The typical projector is constructed spectrally: diagonalize the finite
tensor-power density matrix, keep exactly those eigenspaces whose eigenvalues
are typical, and conjugate the diagonal mask back to the original basis.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

/-! ## Spectral projectors selected by a finite eigenvalue predicate -/

/-- Spectral projector obtained by selecting a decidable predicate on the
eigenbasis of a Hermitian matrix. -/
def spectralPredicateProjector
    (H : CMatrix a) (hH : H.IsHermitian) (p : a → Prop) [DecidablePred p] :
    CMatrix a :=
  (hH.eigenvectorUnitary : CMatrix a) *
    Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0) *
      star (hH.eigenvectorUnitary : CMatrix a)

/-- A spectral predicate projector is positive semidefinite. -/
theorem spectralPredicateProjector_posSemidef
    (H : CMatrix a) (hH : H.IsHermitian) (p : a → Prop) [DecidablePred p] :
    (spectralPredicateProjector H hH p).PosSemidef := by
  classical
  unfold spectralPredicateProjector
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (hH.eigenvectorUnitary : CMatrix a))]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases hi : p i
  · simp [hi]
  · simp [hi]

/-- A spectral predicate projector is Hermitian. -/
theorem spectralPredicateProjector_isHermitian
    (H : CMatrix a) (hH : H.IsHermitian) (p : a → Prop) [DecidablePred p] :
    (spectralPredicateProjector H hH p).IsHermitian :=
  (spectralPredicateProjector_posSemidef H hH p).1

/-- A spectral predicate projector is idempotent. -/
theorem spectralPredicateProjector_idempotent
    (H : CMatrix a) (hH : H.IsHermitian) (p : a → Prop) [DecidablePred p] :
    spectralPredicateProjector H hH p * spectralPredicateProjector H hH p =
      spectralPredicateProjector H hH p := by
  classical
  unfold spectralPredicateProjector
  let U : CMatrix a := hH.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0)
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hH.eigenvectorUnitary]
  have hD : D * D = D := by
    change
      Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0) *
          Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0) =
        Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0)
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : p i <;> simp [hi]
    · simp [Matrix.diagonal, hij]
  calc
    (U * D * star U) * (U * D * star U) =
        U * D * (star U * U) * D * star U := by
          noncomm_ring
    _ = U * D * 1 * D * star U := by rw [hU]
    _ = U * (D * D) * star U := by noncomm_ring
    _ = U * D * star U := by rw [hD]

/-- A spectral predicate projector is bounded above by the identity effect. -/
theorem spectralPredicateProjector_le_one
    (H : CMatrix a) (hH : H.IsHermitian) (p : a → Prop) [DecidablePred p] :
    spectralPredicateProjector H hH p ≤ 1 := by
  classical
  rw [Matrix.le_iff]
  unfold spectralPredicateProjector
  have hOne :
      (1 : CMatrix a) =
        (hH.eigenvectorUnitary : CMatrix a) *
          (1 : CMatrix a) *
            star (hH.eigenvectorUnitary : CMatrix a) := by
    simp
  rw [hOne]
  have hsub :
      (hH.eigenvectorUnitary : CMatrix a) * 1 * star (hH.eigenvectorUnitary : CMatrix a) -
        (hH.eigenvectorUnitary : CMatrix a) *
          Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0) *
            star (hH.eigenvectorUnitary : CMatrix a) =
        (hH.eigenvectorUnitary : CMatrix a) *
          (1 - Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0)) *
            star (hH.eigenvectorUnitary : CMatrix a) := by
    noncomm_ring
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (hH.eigenvectorUnitary : CMatrix a))]
  have hdiag :
      (1 - Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0) : CMatrix a) =
        Matrix.diagonal (fun i => 1 - if p i then (1 : ℂ) else 0) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal, hij]
  rw [hdiag]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases hi : p i
  · simp [hi]
  · simp [hi]

/-- The trace of a spectral predicate projector is the number of selected
eigenbasis directions. -/
theorem spectralPredicateProjector_trace_re
    (H : CMatrix a) (hH : H.IsHermitian) (p : a → Prop) [DecidablePred p] :
    (spectralPredicateProjector H hH p).trace.re =
      ∑ i, if p i then (1 : ℝ) else (0 : ℝ) := by
  classical
  unfold spectralPredicateProjector
  let U : CMatrix a := hH.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0)
  change ((U * D * star U).trace).re = ∑ i, if p i then (1 : ℝ) else 0
  calc
    ((U * D * star U).trace).re = D.trace.re := by
      rw [Matrix.trace_mul_cycle]
      simp [U]
    _ = ∑ i, if p i then (1 : ℝ) else (0 : ℝ) := by
      simp [D, Matrix.trace_diagonal]

/-- The probability weight of a spectral predicate projector against its
underlying Hermitian matrix is the selected eigenvalue sum. -/
theorem spectralPredicateProjector_trace_mul_re
    (H : CMatrix a) (hH : H.IsHermitian) (p : a → Prop) [DecidablePred p] :
    ((H * spectralPredicateProjector H hH p).trace).re =
      ∑ i, if p i then hH.eigenvalues i else (0 : ℝ) := by
  classical
  let U : CMatrix a := hH.eigenvectorUnitary
  let Λ : CMatrix a := Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))
  let P : CMatrix a := Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0)
  have hspec : H = U * Λ * star U := by
    simpa [U, Λ, Function.comp_def, Unitary.conjStarAlgAut_apply]
      using hH.spectral_theorem
  unfold spectralPredicateProjector
  change ((H * (U * P * star U)).trace).re =
    ∑ i, if p i then hH.eigenvalues i else (0 : ℝ)
  conv_lhs => rw [hspec]
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hH.eigenvectorUnitary]
  have hmul :
      (U * Λ * star U) * (U * P * star U) = U * (Λ * P) * star U := by
    calc
      (U * Λ * star U) * (U * P * star U) =
          U * Λ * (star U * U) * P * star U := by
            noncomm_ring
      _ = U * Λ * 1 * P * star U := by rw [hU]
      _ = U * (Λ * P) * star U := by noncomm_ring
  rw [hmul]
  calc
    ((U * (Λ * P) * star U).trace).re = (Λ * P).trace.re := by
      rw [Matrix.trace_mul_cycle]
      simp [U]
    _ = ∑ i, if p i then hH.eigenvalues i else (0 : ℝ) := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : p i <;> simp [hi]

/-- Compressing a Hermitian matrix to a spectral predicate projector is bounded
above by any scalar upper bound on the selected eigenvalues. -/
theorem spectralPredicateProjector_compress_le
    (H : CMatrix a) (hH : H.IsHermitian) (p : a → Prop) [DecidablePred p]
    {c : ℝ} (hp : ∀ i, p i → hH.eigenvalues i ≤ c) :
    spectralPredicateProjector H hH p * H * spectralPredicateProjector H hH p ≤
      (↑c : ℂ) • spectralPredicateProjector H hH p := by
  classical
  let U : CMatrix a := hH.eigenvectorUnitary
  let Λ : CMatrix a := Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))
  let D : CMatrix a := Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0)
  have hspec : H = U * Λ * star U := by
    simpa [U, Λ, Function.comp_def, Unitary.conjStarAlgAut_apply]
      using hH.spectral_theorem
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hH.eigenvectorUnitary]
  set P : CMatrix a := spectralPredicateProjector H hH p with hP_def
  have hP : P = U * D * star U := by
    rw [hP_def]
    rfl
  have hPHP : P * H * P = U * (D * Λ * D) * star U := by
    conv_lhs => rw [hP, hspec]
    conv_lhs =>
      rw [show (U * D * star U) * (U * Λ * star U) =
            U * D * (star U * U) * Λ * star U by noncomm_ring]
      rw [show U * D * (star U * U) * Λ * star U * (U * D * star U) =
            U * D * (star U * U) * Λ * (star U * U) * D * star U by
          noncomm_ring]
      simp only [hU, one_mul, mul_one]
    noncomm_ring
  have hcP : (↑c : ℂ) • P = U * ((↑c : ℂ) • D) * star U := by
    rw [hP]
    calc
      (↑c : ℂ) • (U * D * star U) =
          ((↑c : ℂ) • (U * D)) * star U := by rw [← Matrix.smul_mul]
      _ = (U * ((↑c : ℂ) • D)) * star U := by rw [← Matrix.mul_smul]
      _ = U * ((↑c : ℂ) • D) * star U := rfl
  rw [Matrix.le_iff]
  rw [show (↑c : ℂ) • P - P * H * P =
        U * ((↑c : ℂ) • D - D * Λ * D) * star U by
      rw [hcP, hPHP]
      noncomm_ring]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (hH.eigenvectorUnitary : CMatrix a))]
  have hdiag_inner :
      ((↑c : ℂ) • D - D * Λ * D : CMatrix a) =
        Matrix.diagonal (fun i =>
          if p i then (↑c : ℂ) - hH.eigenvalues i else 0) := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : p i
      all_goals simp [hi, D, Λ, Matrix.diagonal_apply_eq, Matrix.diagonal_mul_diagonal]
    · have hne : ∀ (f : a → ℂ), Matrix.diagonal f i j = 0 :=
        fun f => Matrix.diagonal_apply_ne f hij
      simp only [D, Λ, ← Matrix.diagonal_smul, Matrix.diagonal_mul_diagonal]
      conv_lhs => rw [show ∀ (A B : CMatrix a), (A - B) i j = A i j - B i j
        from fun _ _ => rfl]
      simp only [hne, sub_zero]
  rw [hdiag_inner]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases hi : p i
  · simp only [hi, if_true]
    exact_mod_cast sub_nonneg.mpr (hp i hi)
  · simp only [hi, if_false]
    exact le_refl _

/-- The Schumacher compression rate equals the von Neumann entropy.

rate(rho) = S(rho) = -sum lambda_i log2(lambda_i). -/
def State.schumacherRate (ρ : State a) : ℝ :=
  State.vonNeumann ρ

namespace State

/-- Eigenvalue typicality for the `n`-fold IID state, in bits:
`-log₂ μ` lies within `n δ` of `n S(ρ)`, and zero eigenvalues are excluded. -/
def typicalEigenvalue (ρ : State a) (n : ℕ) (δ μ : ℝ) : Prop :=
  0 < μ ∧ |(-log2 μ) - (n : ℝ) * ρ.vonNeumann| ≤ (n : ℝ) * δ

/-- pack-4 eigenvalue upper bound (equipartition, upper half): every eigenvalue
accepted by the typicality predicate satisfies
`μ ≤ 2^{-n(S(ρ) − δ)}`. This is the upper half of the usual
`2^{-(S + δ)n} ≤ μ ≤ 2^{-(S − δ)n}` equipartition envelope; it follows from
the left inequality of the predicate's centered-log bound. -/
theorem typicalEigenvalue_le_eigenvalueUpperBound
    (ρ : State a) (n : ℕ) (δ μ : ℝ)
    (h : typicalEigenvalue ρ n δ μ) :
    μ ≤ 2 ^ (-((n : ℝ) * ρ.vonNeumann - (n : ℝ) * δ)) := by
  obtain ⟨hμ_pos, habs⟩ := h
  -- Left half of the absolute-value bound:
  --   -((n:ℝ)*δ) ≤ (-log2 μ) - (n:ℝ)*S(ρ),  i.e.  -log2 μ ≥ (n:ℝ)*S(ρ) - (n:ℝ)*δ.
  have hleft : -((n : ℝ) * δ) ≤ (-log2 μ) - (n : ℝ) * ρ.vonNeumann :=
    (abs_le.mp habs).1
  -- Hence log2 μ ≤ -((n:ℝ)*S(ρ) - (n:ℝ)*δ).
  have hlog_le : log2 μ ≤ -((n : ℝ) * ρ.vonNeumann - (n : ℝ) * δ) := by linarith
  have hl2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  -- Convert log2 to Real.log: log2 μ · Real.log 2 = Real.log μ.
  have hid : log2 μ * Real.log 2 = Real.log μ := by
    unfold log2; field_simp
  -- Multiply the log2 inequality by Real.log 2 > 0 to land in Real.log:
  --   Real.log μ ≤ -((n:ℝ)*S(ρ) - (n:ℝ)*δ) · Real.log 2.
  have hlogμ_le : Real.log μ ≤ -((n : ℝ) * ρ.vonNeumann - (n : ℝ) * δ) * Real.log 2 := by
    linarith [mul_le_mul_of_nonneg_right hlog_le hl2_pos.le]
  -- Exponentiate: μ = Real.exp (Real.log μ) ≤ Real.exp (exponent · Real.log 2) = 2^{exponent}.
  have hbase_pos : (0 : ℝ) < 2 := by norm_num
  have hμ_exp : μ = Real.exp (Real.log μ) := (Real.exp_log hμ_pos).symm
  rw [hμ_exp]
  -- `2^{x} = Real.exp (x · Real.log 2)` for the base-2 rpow, so the bound
  -- `Real.log μ ≤ -((n:ℝ)*S − (n:ℝ)*δ) · Real.log 2` exponentiates to
  -- `μ ≤ 2^{-((n:ℝ)*S − (n:ℝ)*δ)}`.
  have hexp : Real.exp (-((n : ℝ) * ρ.vonNeumann - (n : ℝ) * δ) * Real.log 2) =
      2 ^ (-((n : ℝ) * ρ.vonNeumann - (n : ℝ) * δ)) := by
    rw [Real.rpow_def_of_pos hbase_pos, mul_comm]
  refine le_trans (Real.exp_le_exp.mpr hlogμ_le) (le_of_eq hexp)

/-- The finite tensor-power spectral typical-subspace projector. -/
def typicalSubspaceProjector (ρ : State a) (n : ℕ) (δ : ℝ) :
    CMatrix (TensorPower a n) := by
  classical
  let τ := ρ.tensorPower n
  exact spectralPredicateProjector τ.matrix τ.pos.isHermitian
    (fun i => typicalEigenvalue ρ n δ (τ.pos.isHermitian.eigenvalues i))

/-- Number of selected spectral directions, expressed as a real trace count. -/
def typicalSubspaceDimension (ρ : State a) (n : ℕ) (δ : ℝ) : ℝ := by
  classical
  exact ∑ i : TensorPower a n,
    if typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
    then (1 : ℝ) else 0

/-- Spectral probability weight accepted by the typical projector. -/
def typicalSubspaceSpectralWeight (ρ : State a) (n : ℕ) (δ : ℝ) : ℝ := by
  classical
  exact ∑ i : TensorPower a n,
    if typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
    then (ρ.tensorPower n).pos.isHermitian.eigenvalues i else 0

/-- Spectral probability weight rejected by the typical projector. -/
def atypicalSubspaceSpectralWeight (ρ : State a) (n : ℕ) (δ : ℝ) : ℝ := by
  classical
  exact ∑ i : TensorPower a n,
    if ¬ typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
    then (ρ.tensorPower n).pos.isHermitian.eigenvalues i else 0

/-- Second moment of the centered log-eigenvalue random variable for
`ρ^{⊗ n}`. It is the finite spectral-distribution quantity that feeds
Chebyshev-style concentration estimates; separate tensor-product spectrum
lemmas are needed to turn it into an explicit `O(n)` variance bound. -/
def typicalLogDeviationSecondMoment (ρ : State a) (n : ℕ) : ℝ := by
  classical
  exact ∑ i : TensorPower a n,
    let μ := (ρ.tensorPower n).pos.isHermitian.eigenvalues i
    μ * (((-log2 μ) - (n : ℝ) * ρ.vonNeumann) ^ 2)

/-- Eigenvalues of an IID tensor-power density matrix sum to one. -/
theorem tensorPower_eigenvalue_sum (ρ : State a) (n : ℕ) :
    ∑ i : TensorPower a n, (ρ.tensorPower n).pos.isHermitian.eigenvalues i = 1 := by
  have hc :
      (∑ i : TensorPower a n,
          (((ρ.tensorPower n).pos.isHermitian.eigenvalues i : ℝ) : ℂ)) = 1 := by
    exact (ρ.tensorPower n).pos.isHermitian.trace_eq_sum_eigenvalues.symm.trans
      (ρ.tensorPower n).trace_eq_one
  exact Complex.ofReal_injective (by simpa using hc)

/-- The trace-count dimension of the typical subspace is nonnegative. -/
theorem typicalSubspaceDimension_nonneg (ρ : State a) (n : ℕ) (δ : ℝ) :
    0 ≤ ρ.typicalSubspaceDimension n δ := by
  classical
  unfold typicalSubspaceDimension
  exact Finset.sum_nonneg fun i _ => by
    by_cases hi :
      typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
    · simp [hi]
    · simp [hi]

/-- The trace-count dimension of the typical subspace is at most the ambient
finite tensor-power dimension. -/
theorem typicalSubspaceDimension_le_card (ρ : State a) (n : ℕ) (δ : ℝ) :
    ρ.typicalSubspaceDimension n δ ≤ (Fintype.card (TensorPower a n) : ℝ) := by
  classical
  unfold typicalSubspaceDimension
  calc
    (∑ i : TensorPower a n,
        if typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
        then (1 : ℝ) else 0)
        ≤ ∑ _i : TensorPower a n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          by_cases hi :
            typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
          · simp [hi]
          · simp [hi]
    _ = (Fintype.card (TensorPower a n) : ℝ) := by simp

/-- The typical spectral weight is nonnegative. -/
theorem typicalSubspaceSpectralWeight_nonneg (ρ : State a) (n : ℕ) (δ : ℝ) :
    0 ≤ ρ.typicalSubspaceSpectralWeight n δ := by
  classical
  unfold typicalSubspaceSpectralWeight
  apply Finset.sum_nonneg
  intro i _
  by_cases hi :
    typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
  · simp [hi, (ρ.tensorPower n).pos.eigenvalues_nonneg i]
  · simp [hi]

/-- The typical spectral weight is at most one. -/
theorem typicalSubspaceSpectralWeight_le_one (ρ : State a) (n : ℕ) (δ : ℝ) :
    ρ.typicalSubspaceSpectralWeight n δ ≤ 1 := by
  classical
  unfold typicalSubspaceSpectralWeight
  calc
    (∑ i : TensorPower a n,
        if typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
        then (ρ.tensorPower n).pos.isHermitian.eigenvalues i else 0)
        ≤ ∑ i : TensorPower a n, (ρ.tensorPower n).pos.isHermitian.eigenvalues i := by
          apply Finset.sum_le_sum
          intro i _
          by_cases hi :
            typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
          · simp [hi]
          · simp [hi, (ρ.tensorPower n).pos.eigenvalues_nonneg i]
    _ = 1 := tensorPower_eigenvalue_sum ρ n

/-- The atypical spectral weight is nonnegative. -/
theorem atypicalSubspaceSpectralWeight_nonneg (ρ : State a) (n : ℕ) (δ : ℝ) :
    0 ≤ ρ.atypicalSubspaceSpectralWeight n δ := by
  classical
  unfold atypicalSubspaceSpectralWeight
  apply Finset.sum_nonneg
  intro i _
  by_cases hi :
    typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
  · simp [hi]
  · simp [hi, (ρ.tensorPower n).pos.eigenvalues_nonneg i]

/-- The typical and atypical spectral weights partition the tensor-power
state's total spectral weight. -/
theorem typicalSubspaceSpectralWeight_add_atypical (ρ : State a) (n : ℕ) (δ : ℝ) :
    ρ.typicalSubspaceSpectralWeight n δ +
      ρ.atypicalSubspaceSpectralWeight n δ = 1 := by
  classical
  unfold typicalSubspaceSpectralWeight atypicalSubspaceSpectralWeight
  rw [← Finset.sum_add_distrib]
  calc
    (∑ i : TensorPower a n,
        ((if typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
          then (ρ.tensorPower n).pos.isHermitian.eigenvalues i else 0) +
        if ¬ typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
          then (ρ.tensorPower n).pos.isHermitian.eigenvalues i else 0)) =
        ∑ i : TensorPower a n, (ρ.tensorPower n).pos.isHermitian.eigenvalues i := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi :
            typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
          · simp [hi]
          · simp [hi]
    _ = 1 := tensorPower_eigenvalue_sum ρ n

/-- The centered log-eigenvalue second moment is nonnegative. -/
theorem typicalLogDeviationSecondMoment_nonneg (ρ : State a) (n : ℕ) :
    0 ≤ ρ.typicalLogDeviationSecondMoment n := by
  classical
  unfold typicalLogDeviationSecondMoment
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg ((ρ.tensorPower n).pos.eigenvalues_nonneg i) (sq_nonneg _)

/-- Finite spectral Chebyshev bridge for the typical projector.

This is a genuine concentration-form estimate at the spectral-distribution
level: the atypical spectral weight times `(n δ)^2` is controlled by the
centered second moment of the log-eigenvalues of `ρ^{⊗ n}`. A later proof
can combine it with product-spectrum/variance additivity to obtain the usual
i.i.d. typical-subspace concentration bounds. -/
theorem atypicalSubspaceSpectralWeight_mul_sq_le_logDeviationSecondMoment
    (ρ : State a) {n : ℕ} {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) :
    ρ.atypicalSubspaceSpectralWeight n δ * (((n : ℝ) * δ) ^ 2) ≤
      ρ.typicalLogDeviationSecondMoment n := by
  classical
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcpos : 0 < (n : ℝ) * δ := mul_pos hnR hδ
  unfold atypicalSubspaceSpectralWeight typicalLogDeviationSecondMoment
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  let μ := (ρ.tensorPower n).pos.isHermitian.eigenvalues i
  let d := (-log2 μ) - (n : ℝ) * ρ.vonNeumann
  have hμ_nonneg : 0 ≤ μ := by
    simpa [μ] using (ρ.tensorPower n).pos.eigenvalues_nonneg i
  by_cases htyp : typicalEigenvalue ρ n δ μ
  · have hterm_nonneg : 0 ≤ μ * d ^ 2 := mul_nonneg hμ_nonneg (sq_nonneg d)
    simp [htyp, μ, d, hterm_nonneg]
  · by_cases hμ_pos : 0 < μ
    · have hnotle : ¬ |d| ≤ (n : ℝ) * δ := by
        intro hle
        exact htyp ⟨hμ_pos, by simpa [d, μ] using hle⟩
      have hclt : (n : ℝ) * δ < |d| := lt_of_not_ge hnotle
      have hcabs : |(n : ℝ) * δ| ≤ |d| := by
        rw [abs_of_nonneg (le_of_lt hcpos)]
        exact le_of_lt hclt
      have hsq : ((n : ℝ) * δ) ^ 2 ≤ d ^ 2 := by
        have hs := sq_le_sq.mpr hcabs
        simpa [sq_abs] using hs
      have hmul := mul_le_mul_of_nonneg_left hsq hμ_nonneg
      simpa [htyp, μ, d] using hmul
    · have hμ_zero : μ = 0 := le_antisymm (not_lt.mp hμ_pos) hμ_nonneg
      simp [μ, hμ_zero]

/-- Division form of the finite spectral Chebyshev bridge. -/
theorem atypicalSubspaceSpectralWeight_le_logDeviationSecondMoment_div_sq
    (ρ : State a) {n : ℕ} {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) :
    ρ.atypicalSubspaceSpectralWeight n δ ≤
      ρ.typicalLogDeviationSecondMoment n / (((n : ℝ) * δ) ^ 2) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcpos : 0 < (n : ℝ) * δ := mul_pos hnR hδ
  have hc2pos : 0 < (((n : ℝ) * δ) ^ 2) := sq_pos_of_pos hcpos
  rw [le_div_iff₀ hc2pos]
  exact ρ.atypicalSubspaceSpectralWeight_mul_sq_le_logDeviationSecondMoment hn hδ

/-- Lower bound on the accepted typical spectral weight obtained from the
finite spectral Chebyshev bridge. -/
theorem one_sub_logDeviationSecondMoment_div_sq_le_typicalSubspaceSpectralWeight
    (ρ : State a) {n : ℕ} {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) :
    1 - ρ.typicalLogDeviationSecondMoment n / (((n : ℝ) * δ) ^ 2) ≤
      ρ.typicalSubspaceSpectralWeight n δ := by
  have hle := ρ.atypicalSubspaceSpectralWeight_le_logDeviationSecondMoment_div_sq hn hδ
  have hadd := ρ.typicalSubspaceSpectralWeight_add_atypical n δ
  linarith

/-- The typical-subspace projector is positive semidefinite. -/
theorem typicalSubspaceProjector_posSemidef (ρ : State a) (n : ℕ) (δ : ℝ) :
    (ρ.typicalSubspaceProjector n δ).PosSemidef := by
  classical
  unfold typicalSubspaceProjector
  exact spectralPredicateProjector_posSemidef _ _ _

/-- The typical-subspace projector is Hermitian. -/
theorem typicalSubspaceProjector_isHermitian (ρ : State a) (n : ℕ) (δ : ℝ) :
    (ρ.typicalSubspaceProjector n δ).IsHermitian :=
  (ρ.typicalSubspaceProjector_posSemidef n δ).1

/-- The typical-subspace projector is idempotent. -/
theorem typicalSubspaceProjector_idempotent (ρ : State a) (n : ℕ) (δ : ℝ) :
    ρ.typicalSubspaceProjector n δ * ρ.typicalSubspaceProjector n δ =
      ρ.typicalSubspaceProjector n δ := by
  classical
  unfold typicalSubspaceProjector
  exact spectralPredicateProjector_idempotent _ _ _

/-- The typical-subspace projector is bounded by the identity effect. -/
theorem typicalSubspaceProjector_le_one (ρ : State a) (n : ℕ) (δ : ℝ) :
    ρ.typicalSubspaceProjector n δ ≤ 1 := by
  classical
  unfold typicalSubspaceProjector
  exact spectralPredicateProjector_le_one _ _ _

/-- The trace of the typical-subspace projector counts the selected spectral
directions of `ρ^{⊗ n}`. -/
theorem typicalSubspaceProjector_trace_re (ρ : State a) (n : ℕ) (δ : ℝ) :
    (ρ.typicalSubspaceProjector n δ).trace.re =
      ρ.typicalSubspaceDimension n δ := by
  classical
  unfold typicalSubspaceProjector
  unfold typicalSubspaceDimension
  exact spectralPredicateProjector_trace_re _ _ _

/-- The tensor-power state weight accepted by the typical projector is exactly
the selected eigenvalue sum. -/
theorem typicalSubspaceProjector_trace_mul_re (ρ : State a) (n : ℕ) (δ : ℝ) :
    (((ρ.tensorPower n).matrix * ρ.typicalSubspaceProjector n δ).trace).re =
      ρ.typicalSubspaceSpectralWeight n δ := by
  classical
  unfold typicalSubspaceProjector
  unfold typicalSubspaceSpectralWeight
  exact spectralPredicateProjector_trace_mul_re _ _ _

/-- The tensor-power state compressed to its spectral typical subspace is
bounded by the usual typical eigenvalue envelope. -/
theorem typicalSubspaceProjector_tensorPower_compress_le
    (ρ : State a) (n : ℕ) (δ : ℝ) :
    ρ.typicalSubspaceProjector n δ * (ρ.tensorPower n).matrix *
        ρ.typicalSubspaceProjector n δ ≤
      (((((2 : ℝ) ^ (-((n : ℝ) * ρ.vonNeumann - (n : ℝ) * δ))) : ℝ) : ℂ) •
        ρ.typicalSubspaceProjector n δ) := by
  classical
  set c : ℝ := (2 : ℝ) ^ (-((n : ℝ) * ρ.vonNeumann - (n : ℝ) * δ))
  have hp :
      ∀ i : TensorPower a n,
        typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i) →
          (ρ.tensorPower n).pos.isHermitian.eigenvalues i ≤ c := by
    intro i hi
    dsimp [c]
    exact ρ.typicalEigenvalue_le_eigenvalueUpperBound n δ
      ((ρ.tensorPower n).pos.isHermitian.eigenvalues i) hi
  simpa [typicalSubspaceProjector, c] using
    (spectralPredicateProjector_compress_le
      (H := (ρ.tensorPower n).matrix)
      (hH := (ρ.tensorPower n).pos.isHermitian)
      (p := fun i =>
        typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i))
      (c := c) hp)

/-- The bundled projector statement used by downstream theorem routes. -/
def typicalSubspaceProjector_statement
    (ρ : State a) (n : ℕ) (δ : ℝ) : Prop :=
  (ρ.typicalSubspaceProjector n δ).PosSemidef ∧
    (ρ.typicalSubspaceProjector n δ).IsHermitian ∧
    ρ.typicalSubspaceProjector n δ * ρ.typicalSubspaceProjector n δ =
      ρ.typicalSubspaceProjector n δ ∧
    ρ.typicalSubspaceProjector n δ ≤ 1

/-- The finite spectral typical-subspace projector satisfies the bundled
projector statement. -/
theorem typicalSubspaceProjector_statement_proved (ρ : State a) (n : ℕ) (δ : ℝ) :
    ρ.typicalSubspaceProjector_statement n δ := by
  exact ⟨ρ.typicalSubspaceProjector_posSemidef n δ,
    ρ.typicalSubspaceProjector_isHermitian n δ,
    ρ.typicalSubspaceProjector_idempotent n δ,
    ρ.typicalSubspaceProjector_le_one n δ⟩

/-- Complete finite spectral typical-projector estimate package.

This is the closure-level infrastructure consumed by later finite-N AEP
routes: it records the spectral projector construction, rank/probability
envelopes, exact trace identities, and the finite spectral Chebyshev
concentration bridge for the tensor-power density matrix. -/
structure TypicalProjectorEstimates (ρ : State a) (n : ℕ) (δ : ℝ) : Prop where
  projector_statement : ρ.typicalSubspaceProjector_statement n δ
  trace_eq_dimension :
    (ρ.typicalSubspaceProjector n δ).trace.re =
      ρ.typicalSubspaceDimension n δ
  trace_weight_eq_spectralWeight :
    (((ρ.tensorPower n).matrix * ρ.typicalSubspaceProjector n δ).trace).re =
      ρ.typicalSubspaceSpectralWeight n δ
  dimension_nonneg : 0 ≤ ρ.typicalSubspaceDimension n δ
  dimension_le_card :
    ρ.typicalSubspaceDimension n δ ≤ (Fintype.card (TensorPower a n) : ℝ)
  spectralWeight_nonneg : 0 ≤ ρ.typicalSubspaceSpectralWeight n δ
  spectralWeight_le_one : ρ.typicalSubspaceSpectralWeight n δ ≤ 1
  atypicalSpectralWeight_nonneg : 0 ≤ ρ.atypicalSubspaceSpectralWeight n δ
  spectralWeight_partition :
    ρ.typicalSubspaceSpectralWeight n δ +
      ρ.atypicalSubspaceSpectralWeight n δ = 1
  logDeviationSecondMoment_nonneg : 0 ≤ ρ.typicalLogDeviationSecondMoment n
  atypical_mul_sq_le_logDeviationSecondMoment :
    ∀ (_ : 0 < n) (_ : 0 < δ),
      ρ.atypicalSubspaceSpectralWeight n δ * (((n : ℝ) * δ) ^ 2) ≤
        ρ.typicalLogDeviationSecondMoment n
  atypical_le_logDeviationSecondMoment_div_sq :
    ∀ (_ : 0 < n) (_ : 0 < δ),
      ρ.atypicalSubspaceSpectralWeight n δ ≤
        ρ.typicalLogDeviationSecondMoment n / (((n : ℝ) * δ) ^ 2)
  typical_weight_lower_bound :
    ∀ (_ : 0 < n) (_ : 0 < δ),
      1 - ρ.typicalLogDeviationSecondMoment n / (((n : ℝ) * δ) ^ 2) ≤
        ρ.typicalSubspaceSpectralWeight n δ

/-- The finite spectral typical-subspace projector satisfies the complete
estimate package required by the AEP proof route. -/
theorem typicalSubspaceProjector_estimates (ρ : State a) (n : ℕ) (δ : ℝ) :
    ρ.TypicalProjectorEstimates n δ where
  projector_statement := ρ.typicalSubspaceProjector_statement_proved n δ
  trace_eq_dimension := ρ.typicalSubspaceProjector_trace_re n δ
  trace_weight_eq_spectralWeight := ρ.typicalSubspaceProjector_trace_mul_re n δ
  dimension_nonneg := ρ.typicalSubspaceDimension_nonneg n δ
  dimension_le_card := ρ.typicalSubspaceDimension_le_card n δ
  spectralWeight_nonneg := ρ.typicalSubspaceSpectralWeight_nonneg n δ
  spectralWeight_le_one := ρ.typicalSubspaceSpectralWeight_le_one n δ
  atypicalSpectralWeight_nonneg := ρ.atypicalSubspaceSpectralWeight_nonneg n δ
  spectralWeight_partition := ρ.typicalSubspaceSpectralWeight_add_atypical n δ
  logDeviationSecondMoment_nonneg := ρ.typicalLogDeviationSecondMoment_nonneg n
  atypical_mul_sq_le_logDeviationSecondMoment := by
    intro hn hδ
    exact ρ.atypicalSubspaceSpectralWeight_mul_sq_le_logDeviationSecondMoment hn hδ
  atypical_le_logDeviationSecondMoment_div_sq := by
    intro hn hδ
    exact ρ.atypicalSubspaceSpectralWeight_le_logDeviationSecondMoment_div_sq hn hδ
  typical_weight_lower_bound := by
    intro hn hδ
    exact ρ.one_sub_logDeviationSecondMoment_div_sq_le_typicalSubspaceSpectralWeight hn hδ

/-! ## Linear-in-`n` variance bound and high-probability `1 − ε` form

The centered log-eigenvalue second moment of `ρ^{⊗ n}` is exactly `n` times
the single-system second moment. The eigenvalues of `ρ^{⊗ n}` are the
`n`-fold products `μ = μ₁ … μₙ` of the eigenvalues of `ρ` (the
`eigenvalueMultiset_tensorPower` keystone), so under the product distribution
the per-symbol centered deviations `(-log₂ μⱼ − S(ρ))` are independent with
mean `0`. The variance-of-a-sum identity collapses the cross-terms, leaving
`n · typicalLogDeviationSecondMoment ρ 1` [Wilde2011Qst, qit-notes.tex:33634-33808].

The proof mirrors the entropy-additivity route: a per-element centered-
deviation product split (a `Real.log_mul` rewrite, with the `0 log 0 := 0`
convention absorbing zero eigenvalues through the `μ` prefactor), a
single-step Kronecker-bind inner-sum identity (the variance-of-a-sum step,
closed by `ring`), and an induction on `n`.
-/

/-- The per-element centered log deviation `cd(S, μ) = -log2 μ − S`. -/
private def centeredLogDev (S μ : ℝ) : ℝ := -log2 μ - S

/-- For nonneg `x, y` with `x * y > 0`, the centered log deviation of the
product splits additively:
`cd(Sx + Sy, x * y) = cd(Sx, x) + cd(Sy, y)`.
The strict-positivity guard keeps `Real.log_mul` applicable. -/
private lemma centeredLogDev_prod {x y Sx Sy : ℝ}
    (hxnn : 0 ≤ x) (hynn : 0 ≤ y) (hxy : 0 < x * y) :
    centeredLogDev (Sx + Sy) (x * y) =
      centeredLogDev Sx x + centeredLogDev Sy y := by
  have hxp : 0 < x := by
    rcases lt_or_eq_of_le hxnn with h | h
    · exact h
    · nlinarith
  have hyp : 0 < y := by
    rcases lt_or_eq_of_le hynn with h | h
    · exact h
    · nlinarith
  have hlog2 : log2 (x * y) = log2 x + log2 y := by
    simp only [log2, log2]
    rw [Real.log_mul (ne_of_gt hxp) (ne_of_gt hyp)]; ring
  simp only [centeredLogDev, centeredLogDev, centeredLogDev]
  rw [hlog2]; ring

/-- The single-system spectrum has mean-zero centered log deviation:
`Σ_{x ∈ spec(ρ)} x · cd(S(ρ), x) = 0`. This centering is what collapses the
variance-of-a-sum cross-terms. -/
private lemma eigenvalueMultiset_centered_sum (ρ : State a) :
    (Multiset.map (fun x => x * centeredLogDev ρ.vonNeumann x)
      (eigenvalueMultiset ρ.pos.isHermitian)).sum = 0 := by
  -- `Σ x · (-log2 x − S) = -Σ xlog2 x − S · Σ x = S − S · 1 = 0`.
  have hS : ρ.vonNeumann = -((eigenvalueMultiset ρ.pos.isHermitian).map xlog2).sum :=
    vonNeumann_eq_neg_sum_eigenvalueMultiset ρ
  have hSum : (eigenvalueMultiset ρ.pos.isHermitian).sum = 1 :=
    eigenvalueMultiset_sum ρ
  -- Distribute `x . (-log2 x - S) = -(x . log2 x) - x . S` per element.
  rw [Multiset.map_congr rfl (fun x _ => by
      show x * centeredLogDev ρ.vonNeumann x =
        -(x * log2 x) + -(x * ρ.vonNeumann)
      simp only [centeredLogDev]
      ring)]
  rw [multiset_sum_add_distrib]
  -- First summand: `Σ -(x·log2 x) = -Σ xlog2 x` after `x·log2 x = xlog2 x`.
  have hxl : ∀ x : ℝ, x * log2 x = xlog2 x := fun x => by
    by_cases hzx : x = 0 <;> simp [xlog2, hzx]
  -- Pull the negation out of each summand (`simp` handles `Σ -f = -(Σ f)`).
  simp only [Multiset.sum_map_neg, Multiset.map_congr rfl (fun x _ => hxl x),
    Multiset.map_congr rfl (fun x _ =>
      (show -(x * ρ.vonNeumann) = x * (-ρ.vonNeumann) from by ring))]
  rw [multiset_sum_mul_const, Multiset.map_id', hSum, ← hS]
  ring

/-! ### Inner-sum variance-of-a-sum step

`Σ_{y ∈ t} (x · y) · (px + py)² = x · px² · (Σ t) + 2 · (x · px) · (Σ_t y·py)
+ x · (Σ_t y · py²)`, a pure polynomial identity over a multiset (proved by
induction with `ring`). Here `px`, `py` are arbitrary per-element reals. -/

private lemma inner_variance_sum (t : Multiset ℝ) (x px : ℝ) (g : ℝ → ℝ) :
    (t.map fun y => x * y * (px + g y) ^ 2).sum =
      x * px ^ 2 * t.sum +
        2 * (x * px) * (t.map fun y => y * g y).sum +
        x * (t.map fun y => y * g y ^ 2).sum := by
  classical
  induction t using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih]
    simp only [Multiset.map_cons, Multiset.sum_cons]
    ring

/-! ### Scaled-by-`(Real.log 2)²` linearity over the tensor-power spectrum -/

/-- Kronecker-bind second-moment step (variance-of-a-sum). For multisets
`s, t`, per-element reals `px : ℝ` (for `x ∈ s`) and `gy` (for `y ∈ t`), if
the product-eigenvalue centered deviation splits as
`(x * y) · q(x * y)² = (x * y) · (px + gy)²` for every `(x, y)`, then
`Σ_{(x,y)} (x*y)·q(x*y)² = (Σ t)·(Σ_s x·px²) + 2·(Σ_s x·px)·(Σ_t y·gy) +
(Σ s)·(Σ_t y·gy²)`. This is a pure polynomial-multiset identity (the square
expands and the `x`, `y` prefactors factor out of the disjoint sums), closed
by `Multiset.induction_on` with `ring` at each step. -/

private lemma kronecker_second_moment_step
    (s t : Multiset ℝ) (q : ℝ → ℝ) (pxOf : ℝ → ℝ) (gyOf : ℝ → ℝ)
    (hsplit : ∀ x ∈ s, ∀ y ∈ t,
      x * y * q (x * y) ^ 2 = x * y * (pxOf x + gyOf y) ^ 2) :
    (Multiset.map (fun μ => μ * q μ ^ 2)
      (s.bind fun x => t.map fun y => x * y)).sum =
      t.sum * (s.map fun x => x * pxOf x ^ 2).sum +
        2 * (s.map fun x => x * pxOf x).sum * (t.map fun y => y * gyOf y).sum +
        s.sum * (t.map fun y => y * gyOf y ^ 2).sum := by
  classical
  induction s using Multiset.induction_on with
  | empty =>
    simp
  | cons a s ih =>
    -- `hsplit` specialized to the tail `s` (for the IH).
    have hsplit_s : ∀ x ∈ s, ∀ y ∈ t,
        x * y * q (x * y) ^ 2 = x * y * (pxOf x + gyOf y) ^ 2 := by
      intro x hx y hy
      exact hsplit x (Multiset.mem_cons.mpr (Or.inr hx)) y hy
    rw [Multiset.cons_bind, Multiset.map_add, Multiset.sum_add, ih hsplit_s]
    -- Inner sum over `y ∈ t` of `a·y·q(a·y)²`, split per `hsplit`.
    have hinner : (t.map fun y => a * y * q (a * y) ^ 2).sum =
        a * (pxOf a) ^ 2 * t.sum +
          2 * (a * pxOf a) * (t.map fun y => y * gyOf y).sum +
          a * (t.map fun y => y * gyOf y ^ 2).sum := by
      have hsp : ∀ y ∈ t,
          a * y * q (a * y) ^ 2 = a * y * (pxOf a + gyOf y) ^ 2 :=
        fun y hy => hsplit a (Multiset.mem_cons.mpr (Or.inl rfl)) y hy
      rw [Multiset.map_congr rfl hsp]
      exact inner_variance_sum t a (pxOf a) gyOf
    -- Flatten `map f (map g t)` into `map (fun y => (a·y)·q(a·y)²) t` so
    -- `hinner` matches.
    rw [Multiset.map_map,
        show (fun μ => μ * q μ ^ 2) ∘ (fun y => a * y) =
          (fun y => a * y * q (a * y) ^ 2) from rfl]
    rw [hinner]
    simp only [Multiset.map_cons, Multiset.sum_cons]
    ring

/-- The second-moment sum over the tensor-power spectrum, with each centered
deviation scaled by `Real.log 2` (so `Real.log_mul` linearizes the log of
products; the `0 log 0 := 0` convention absorbs zero eigenvalues through the
`μ` prefactor), equals `n` times the single-system analogue. -/
private lemma secondMoment_tensorPower_scaled (ρ : State a) (n : ℕ) :
    (Multiset.map (fun μ => μ *
        (Real.log 2 * centeredLogDev ((n : ℝ) * ρ.vonNeumann) μ) ^ 2)
      (tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) n)).sum =
      n * (Multiset.map (fun x => x *
        (Real.log 2 * centeredLogDev ρ.vonNeumann x) ^ 2)
        (eigenvalueMultiset ρ.pos.isHermitian)).sum := by
  induction n with
  | zero =>
    rw [tensorPowerMultiset_zero]
    simp only [Multiset.map_singleton, Multiset.sum_singleton,
      Nat.cast_zero, zero_mul, centeredLogDev, log2, Real.log_one]
    ring
  | succ k ih =>
    rw [tensorPowerMultiset_succ]
    -- Per-element product split: `(x*y)·(L·cd((k+1)S, x*y))² =
    -- (x*y)·(L·cd(S,x) + L·cd(kS,y))²`. The `(x*y)` prefactor absorbs the
    -- zero-eigenvalue case; the strictly-positive case uses `Real.log_mul`.
    have hsplit : ∀ x ∈ eigenvalueMultiset ρ.pos.isHermitian,
        ∀ y ∈ tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) k,
          x * y * (Real.log 2 * centeredLogDev (↑(k + 1) * ρ.vonNeumann) (x * y)) ^ 2 =
          x * y * (Real.log 2 * centeredLogDev ρ.vonNeumann x +
                    Real.log 2 * centeredLogDev ((k : ℝ) * ρ.vonNeumann) y) ^ 2 := by
      intro x hx y hy
      have hxnn : 0 ≤ x := eigenvalueMultiset_nonneg ρ x hx
      have hynn : 0 ≤ y := tensorPowerMultiset_nonneg ρ k y hy
      by_cases hxy : x * y = 0
      · rw [hxy, zero_mul, zero_mul]
      · have hpos : 0 < x * y :=
          lt_of_le_of_ne (mul_nonneg hxnn hynn) (Ne.symm hxy)
        rw [show ((↑(k + 1) : ℝ)) * ρ.vonNeumann =
              (ρ.vonNeumann + (k : ℝ) * ρ.vonNeumann) from by push_cast; ring]
        rw [centeredLogDev_prod hxnn hynn hpos]
        ring
    -- Apply the variance-of-a-sum step.
    rw [kronecker_second_moment_step
        (eigenvalueMultiset ρ.pos.isHermitian)
        (tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) k)
        (fun μ => Real.log 2 * centeredLogDev (↑(k + 1) * ρ.vonNeumann) μ)
        (fun x => Real.log 2 * centeredLogDev ρ.vonNeumann x)
        (fun y => Real.log 2 * centeredLogDev ((k : ℝ) * ρ.vonNeumann) y)
        hsplit]
    -- Trace-1 sums: `s.sum = 1`, `TP.sum = 1`.
    rw [eigenvalueMultiset_sum, tensorPowerMultiset_sum]
    -- Cross-term vanishes: `Σ_x x·(L·cd(S,x)) = L · Σ_x x·cd(S,x) = L·0 = 0`.
    have hCentered : (Multiset.map (fun x => x *
        (Real.log 2 * centeredLogDev ρ.vonNeumann x))
        (eigenvalueMultiset ρ.pos.isHermitian)).sum = 0 := by
      have h := eigenvalueMultiset_centered_sum ρ
      -- Reorder the summand to `(Real.log 2) * (x · cd)` so `sum_map_mul_left`
      -- pulls the `Real.log 2` factor out of the sum.
      rw [Multiset.map_congr rfl (fun x _ =>
            (show x * (Real.log 2 * centeredLogDev ρ.vonNeumann x) =
              Real.log 2 * (x * centeredLogDev ρ.vonNeumann x) from by ring))]
      rw [Multiset.sum_map_mul_left, h]
      ring
    -- Recognize the IH in the surviving `k`-fold second moment, then close by
    -- polynomial arithmetic (`hCentered` kills the cross-term).
    rw [show ((tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) k).map
          (fun y => y * (Real.log 2 * centeredLogDev ((k : ℝ) * ρ.vonNeumann) y) ^ 2)).sum
        = (Multiset.map (fun μ => μ *
            (Real.log 2 * centeredLogDev ((k : ℝ) * ρ.vonNeumann) μ) ^ 2)
          (tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) k)).sum from rfl]
    rw [ih]
    -- The cross-term's first factor is exactly `hCentered`; rewrite to `0`.
    rw [hCentered, mul_zero, zero_mul]
    push_cast
    ring

/-- Bridge: the `Finset.univ` definition of `typicalLogDeviationSecondMoment`
is the multiset sum over the tensor-power spectrum, with bare (unscaled)
centered deviations. -/
private lemma typicalLogDeviationSecondMoment_eq_multiset (ρ : State a) (m : ℕ) :
    ρ.typicalLogDeviationSecondMoment m =
      (Multiset.map (fun μ => μ *
        (centeredLogDev ((m : ℝ) * ρ.vonNeumann) μ) ^ 2)
        (tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) m)).sum := by
  classical
  unfold typicalLogDeviationSecondMoment
  -- The `let μ := ...` summand zeta-reduces to its body; restate without `let`.
  show (∑ i : TensorPower a m,
      (ρ.tensorPower m).pos.isHermitian.eigenvalues i *
        (-log2 ((ρ.tensorPower m).pos.isHermitian.eigenvalues i) -
          (m : ℝ) * ρ.vonNeumann) ^ 2) =
    (Multiset.map (fun μ => μ *
      (centeredLogDev ((m : ℝ) * ρ.vonNeumann) μ) ^ 2)
      (tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) m)).sum
  -- Convert the `Finset` sum to a multiset sum over `Finset.univ.val`.
  rw [Finset.sum_eq_multiset_sum]
  -- Restate the LHS map in composed form `((fun μ => μ·body μ) ∘ eig)`.
  conv_lhs => rw [show (fun (i : TensorPower a m) =>
        (ρ.tensorPower m).pos.isHermitian.eigenvalues i *
          (-log2 ((ρ.tensorPower m).pos.isHermitian.eigenvalues i) -
            (m : ℝ) * ρ.vonNeumann) ^ 2) =
      (fun μ => μ * (-log2 μ - (m : ℝ) * ρ.vonNeumann) ^ 2) ∘
        (ρ.tensorPower m).pos.isHermitian.eigenvalues from rfl]
  -- `(fun μ => μ·body μ) ∘ eig` unfolds to `map (fun μ => μ·body μ) (map eig)`.
  rw [← Multiset.map_map]
  -- `map eig univ.val = eigenvalueMultiset (tensorPower.pos.isHermitian)`.
  rw [show (Multiset.map (ρ.tensorPower m).pos.isHermitian.eigenvalues
        Finset.univ.val) =
      eigenvalueMultiset ((ρ.tensorPower m).pos.isHermitian) from rfl]
  -- Apply the tensor-power spectrum keystone.
  rw [eigenvalueMultiset_tensorPower ρ m]
  rfl

/-- The centered log-eigenvalue second moment is exactly linear in `n`:
`typicalLogDeviationSecondMoment ρ n = n · typicalLogDeviationSecondMoment ρ 1`.

The eigenvalues of `ρ^{⊗ n}` are the `n`-fold products of the eigenvalues of
`ρ` (`eigenvalueMultiset_tensorPower`); under the product distribution the
per-symbol centered deviations `(-log₂ μⱼ − S(ρ))` are independent with mean
`0`, so the variance-of-a-sum identity collapses the cross-terms and leaves
`n` copies of the single-system second moment
[Wilde2011Qst, qit-notes.tex:33634-33808]. -/
theorem typicalLogDeviationSecondMoment_tensorPower (ρ : State a) (n : ℕ) :
    ρ.typicalLogDeviationSecondMoment n =
      n * ρ.typicalLogDeviationSecondMoment 1 := by
  rw [typicalLogDeviationSecondMoment_eq_multiset ρ n,
      typicalLogDeviationSecondMoment_eq_multiset ρ 1]
  -- Both sides are bare-`cd` multiset sums. Relate to the `(L·cd)²` scaled
  -- form via the factor `μ · (L·cd)² = L² · (μ · cd²)`.
  have hFactor : ∀ (s : Multiset ℝ) (C : ℝ),
      (s.map (fun μ => μ * (Real.log 2 * centeredLogDev C μ) ^ 2)).sum =
        (Real.log 2) ^ 2 *
          (s.map (fun μ => μ * (centeredLogDev C μ) ^ 2)).sum := by
    intro s C
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih,
          Multiset.map_cons, Multiset.sum_cons]; ring
  have hL2 : (Real.log 2) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  -- The scaled workhorse: `Σ_{μ ∈ TP_n} μ·(L·cd(nS,μ))² = n·Σ_{x∈s} x·(L·cd(S,x))²`.
  have hScaleN := secondMoment_tensorPower_scaled ρ n
  -- Fold both `(L·cd)²` sums into `L² ·` bare-`cd²` sums, by instantiating
  -- `hFactor` explicitly at each multiset/centering pair (avoiding the
  -- ambiguity of a bare `rw [hFactor] at hScaleN`).
  have hFn : (Multiset.map (fun μ => μ *
        (Real.log 2 * centeredLogDev ((n : ℝ) * ρ.vonNeumann) μ) ^ 2)
        (tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) n)).sum =
      (Real.log 2) ^ 2 *
        (Multiset.map (fun μ => μ *
          (centeredLogDev ((n : ℝ) * ρ.vonNeumann) μ) ^ 2)
          (tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) n)).sum :=
    hFactor _ _
  have hF1 : (Multiset.map (fun x => x *
        (Real.log 2 * centeredLogDev ρ.vonNeumann x) ^ 2)
        (eigenvalueMultiset ρ.pos.isHermitian)).sum =
      (Real.log 2) ^ 2 *
        (Multiset.map (fun x => x *
          (centeredLogDev ρ.vonNeumann x) ^ 2)
          (eigenvalueMultiset ρ.pos.isHermitian)).sum :=
    hFactor _ _
  -- Substitute into `hScaleN`: `L² · T_n = n · (L² · T_1)`.
  have hKey : (Real.log 2) ^ 2 *
      (Multiset.map (fun μ => μ *
        (centeredLogDev ((n : ℝ) * ρ.vonNeumann) μ) ^ 2)
        (tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) n)).sum =
      (Real.log 2) ^ 2 *
        ((n : ℝ) * (Multiset.map (fun x => x *
          (centeredLogDev ρ.vonNeumann x) ^ 2)
          (eigenvalueMultiset ρ.pos.isHermitian)).sum) := by
    rw [← hFn, hScaleN, hF1]; ring
  -- Cancel the left factor `L² ≠ 0`.
  have hEq :
      (Multiset.map (fun μ => μ *
        (centeredLogDev ((n : ℝ) * ρ.vonNeumann) μ) ^ 2)
        (tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) n)).sum =
      (n : ℝ) * (Multiset.map (fun x => x *
        (centeredLogDev ρ.vonNeumann x) ^ 2)
        (eigenvalueMultiset ρ.pos.isHermitian)).sum :=
    mul_left_cancel₀ hL2 hKey
  -- The LHS of the goal is exactly `hEq`'s LHS; close by `hEq` after
  -- recognizing the single-system RHS.
  conv_lhs => rw [hEq]
  -- The goal RHS is `n · Σ_{μ ∈ TP_1} μ·cd((1:ℝ)*S, μ)²`. Recognize
  -- `TP s 1 = s` and `(1:ℝ)*S = S`.
  have hTP1 : tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) 1 =
      eigenvalueMultiset ρ.pos.isHermitian := by
    -- `tensorPowerMultiset s 1 = s.bind (fun x => {1}.map (fun y => x*y))`,
    -- and `{1}.map (· * x) = {x}`, so each `x` maps to the singleton `{x}`;
    -- the bind over `s` of singletons is `s` itself.
    rw [tensorPowerMultiset_succ, tensorPowerMultiset_zero]
    induction (eigenvalueMultiset ρ.pos.isHermitian) using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      rw [Multiset.cons_bind, Multiset.map_singleton, ih]
      simp only [mul_one, Multiset.singleton_add]
  rw [hTP1]
  -- Both sides agree: unfold `centeredLogDev`, reduce `↑1 → 1`, then `1*S = S`.
  simp only [centeredLogDev, Nat.cast_one, one_mul]

/-- The centered log-eigenvalue second moment is bounded by a constant
(the single-system second moment) times `n`. This is the linear-in-`n`
variance bound consumed by the high-probability form below. -/
theorem typicalLogDeviationSecondMoment_le_tensorPower (ρ : State a) (n : ℕ) :
    ρ.typicalLogDeviationSecondMoment n ≤
      n * ρ.typicalLogDeviationSecondMoment 1 :=
  (ρ.typicalLogDeviationSecondMoment_tensorPower n).le

/-- High-probability `1 − ε` form of the typical-subspace weight: for any
`0 < ε, δ`, once `n` reaches the threshold `C / (ε · δ²)` (with
`C = typicalLogDeviationSecondMoment ρ 1`), the typical spectral weight is at
least `1 − ε` [Wilde2011Qst, qit-notes.tex:33634-33808].

Combining the linear-in-`n` variance bound with the spectral Chebyshev
bridge gives `atypicalWeight ≤ (n · C) / (n δ)² = C / (n · δ²) ≤ ε` once
`n ≥ C / (ε · δ²)`, hence `typicalWeight = 1 − atypicalWeight ≥ 1 − ε`. -/
theorem typicalSubspaceSpectralWeight_high_probability
    (ρ : State a) {n : ℕ} {δ ε : ℝ} (hn : 0 < n) (hδ : 0 < δ) (hε : 0 < ε)
    (hthresh : (ρ.typicalLogDeviationSecondMoment 1 / (ε * δ ^ 2)) ≤ n) :
    1 - ε ≤ ρ.typicalSubspaceSpectralWeight n δ := by
  -- Chebyshev lower bound.
  refine le_trans ?_
    (ρ.one_sub_logDeviationSecondMoment_div_sq_le_typicalSubspaceSpectralWeight hn hδ)
  -- It suffices to show `secondMoment n / (n δ)² ≤ ε`.
  -- Substitute the linearity `secondMoment n = (n : ℝ) · C`.
  have hLin : ρ.typicalLogDeviationSecondMoment n =
      (n : ℝ) * ρ.typicalLogDeviationSecondMoment 1 :=
    by exact_mod_cast ρ.typicalLogDeviationSecondMoment_tensorPower n
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hδ2pos : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hεδ2pos : 0 < ε * δ ^ 2 := mul_pos hε hδ2pos
  -- From the threshold `C / (ε δ²) ≤ (n : ℝ)`: `C ≤ (n : ℝ) · (ε δ²)`.
  have hCle : ρ.typicalLogDeviationSecondMoment 1 ≤ (n : ℝ) * (ε * δ ^ 2) := by
    have := (div_le_iff₀ hεδ2pos).mp (by exact_mod_cast hthresh)
    linarith [show (n : ℝ) * (ε * δ ^ 2) = (n : ℝ) * ε * δ ^ 2 from by ring]
  -- Reduce `(n · C) / ((n:ℝ)·δ)²` to `C / ((n:ℝ)·δ²) ≤ ε`.
  have hred : (n : ℝ) * ρ.typicalLogDeviationSecondMoment 1 / ((n : ℝ) * δ) ^ 2 =
      ρ.typicalLogDeviationSecondMoment 1 / ((n : ℝ) * δ ^ 2) := by field_simp
  rw [hLin, hred]
  -- Goal: `1 - ε ≤ 1 - C / ((n:ℝ)·δ²)`, i.e. `C / ((n:ℝ)·δ²) ≤ ε`.
  have hrearrange : ρ.typicalLogDeviationSecondMoment 1 ≤ ε * ((n : ℝ) * δ ^ 2) := by
    linarith [show (n : ℝ) * (ε * δ ^ 2) = ε * ((n : ℝ) * δ ^ 2) from by ring]
  linarith [(div_le_iff₀ (mul_pos hnR hδ2pos)).mpr hrearrange]


/-- Dual form: the atypical spectral weight is at most `ε` past the
threshold `n ≥ C / (ε δ²)`. -/
theorem atypicalSubspaceSpectralWeight_high_probability
    (ρ : State a) {n : ℕ} {δ ε : ℝ} (hn : 0 < n) (hδ : 0 < δ) (hε : 0 < ε)
    (hthresh : (ρ.typicalLogDeviationSecondMoment 1 / (ε * δ ^ 2)) ≤ n) :
    ρ.atypicalSubspaceSpectralWeight n δ ≤ ε := by
  have hpart := ρ.typicalSubspaceSpectralWeight_add_atypical n δ
  have htyp := ρ.typicalSubspaceSpectralWeight_high_probability hn hδ hε hthresh
  linarith

/-! ## AEP typicality estimates for Schumacher direct achievability

These are the asymptotic typical-subspace estimates consumed by the Schumacher
direct coding theorem [Wilde2011Qst, qit-notes.tex:31457-31598]:

  * **(A)** Lower eigenvalue bound (lower half of the equipartition envelope).
  * **(B)** Typical-subspace dimension rate bound `|T_δ^n| ≤ 2^{n(S+δ)}`.
  * **(C)** Exact tensor-power second-moment identity
    `typicalLogDeviationSecondMoment ρ n = n · singleCopyLogDeviationSecondMoment ρ`.
  * **(D)** Atypical spectral weight tends to zero: `atypicalWeight → 0`.
  * **(E)** Typical spectral weight tends to one: `typicalWeight → 1`. -/

open Filter

/-- pack-4 eigenvalue lower bound (equipartition, lower half): every eigenvalue
accepted by the typicality predicate satisfies `2^{-n(S(ρ)+δ)} ≤ μ`.

This is the lower half of the usual `2^{-(S+δ)n} ≤ μ ≤ 2^{-(S−δ)n}`
equipartition envelope; it follows from the right inequality of the
predicate's centered-log bound, by exponentiating with `2^{x} = exp(x·log 2)`
[Wilde2011Qst, qit-notes.tex:31457-31598]. -/
theorem typicalEigenvalue_ge_eigenvalueLowerBound
    (ρ : State a) (n : ℕ) (δ μ : ℝ) (h : typicalEigenvalue ρ n δ μ) :
    2 ^ (-((n : ℝ) * ρ.vonNeumann + (n : ℝ) * δ)) ≤ μ := by
  obtain ⟨hμ_pos, habs⟩ := h
  -- Right half of the absolute-value bound:
  --   (-log2 μ) - (n:ℝ)*S(ρ) ≤ (n:ℝ)*δ, i.e.  -log2 μ ≤ (n:ℝ)*S(ρ) + (n:ℝ)*δ.
  have hright : (-log2 μ) - (n : ℝ) * ρ.vonNeumann ≤ (n : ℝ) * δ :=
    (abs_le.mp habs).2
  -- Hence `log2 μ ≥ -((n:ℝ)*S(ρ) + (n:ℝ)*δ)`.
  have hlog_ge : -((n : ℝ) * ρ.vonNeumann + (n : ℝ) * δ) ≤ log2 μ := by linarith
  have hl2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  -- Convert log2 to Real.log: `log2 μ · Real.log 2 = Real.log μ`.
  have hid : log2 μ * Real.log 2 = Real.log μ := by
    unfold log2; field_simp
  -- Multiply the log2 inequality by `Real.log 2 > 0` to land in `Real.log`:
  --   `-((n:ℝ)*(S+δ)) · Real.log 2 ≤ Real.log μ`.
  have hlogμ_ge : -((n : ℝ) * ρ.vonNeumann + (n : ℝ) * δ) * Real.log 2 ≤ Real.log μ := by
    linarith [mul_le_mul_of_nonneg_right hlog_ge hl2_pos.le]
  have hbase_pos : (0 : ℝ) < 2 := by norm_num
  -- `2^{x} = Real.exp (x · Real.log 2)`; `μ = Real.exp (Real.log μ)`.
  have hexp_eq : 2 ^ (-((n : ℝ) * ρ.vonNeumann + (n : ℝ) * δ)) =
      Real.exp (-((n : ℝ) * ρ.vonNeumann + (n : ℝ) * δ) * Real.log 2) := by
    rw [Real.rpow_def_of_pos hbase_pos, mul_comm]
  rw [hexp_eq, ← Real.exp_log hμ_pos]
  exact Real.exp_le_exp.mpr hlogμ_ge

/-- The single-copy centered log-eigenvalue second moment
`Σ_{j} λ_j · (-log2 λ_j − S(ρ))²`, the per-system variance consumed by the
tensor-power second-moment identity. -/
noncomputable def singleCopyLogDeviationSecondMoment (ρ : State a) : ℝ :=
  ∑ i : a, (ρ.pos.isHermitian.eigenvalues i) *
    ((-log2 (ρ.pos.isHermitian.eigenvalues i)) - ρ.vonNeumann) ^ 2

/-- The single-copy second moment is nonnegative (sum of `λ·(·)²` with `λ ≥ 0`). -/
theorem singleCopyLogDeviationSecondMoment_nonneg (ρ : State a) :
    0 ≤ ρ.singleCopyLogDeviationSecondMoment := by
  unfold singleCopyLogDeviationSecondMoment
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (ρ.pos.eigenvalues_nonneg i) (sq_nonneg _)

/-- The `n = 1` tensor-power multiset is the original spectrum:
`tensorPowerMultiset s 1 = s`. -/
private lemma tensorPowerMultiset_one (s : Multiset ℝ) :
    tensorPowerMultiset s 1 = s := by
  rw [tensorPowerMultiset_succ, tensorPowerMultiset_zero]
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_bind, Multiset.map_singleton, ih]
    simp only [mul_one, Multiset.singleton_add]

/-- Bridge: the `Finset.univ` definition of `singleCopyLogDeviationSecondMoment`
is the multiset sum over the eigenvalue spectrum, with bare (unscaled) centered
deviations. -/
private lemma singleCopyLogDeviationSecondMoment_eq_multiset (ρ : State a) :
    ρ.singleCopyLogDeviationSecondMoment =
      (Multiset.map (fun μ => μ * (centeredLogDev ρ.vonNeumann μ) ^ 2)
        (eigenvalueMultiset ρ.pos.isHermitian)).sum := by
  unfold singleCopyLogDeviationSecondMoment
  rw [Finset.sum_eq_multiset_sum]
  conv_lhs => rw [show (fun (i : a) =>
        (ρ.pos.isHermitian.eigenvalues i) *
          ((-log2 (ρ.pos.isHermitian.eigenvalues i)) - ρ.vonNeumann) ^ 2) =
      (fun μ => μ * (centeredLogDev ρ.vonNeumann μ) ^ 2) ∘
        ρ.pos.isHermitian.eigenvalues from rfl]
  rw [← Multiset.map_map]
  rfl

/-- The centered log-eigenvalue second moment is exactly linear in `n`:
`typicalLogDeviationSecondMoment ρ n = n · singleCopyLogDeviationSecondMoment ρ`.

The eigenvalues of `ρ^{⊗ n}` are the `n`-fold products of the eigenvalues of
`ρ` (`eigenvalueMultiset_tensorPower`); under the product distribution the
per-symbol centered deviations `(-log₂ μⱼ − S(ρ))` are independent with mean
`0`, so the variance-of-a-sum identity collapses the cross-terms and leaves
`n` copies of the single-system second moment
[Wilde2011Qst, qit-notes.tex:33634-33808]. -/
theorem typicalLogDeviationSecondMoment_eq (ρ : State a) (n : ℕ) :
    ρ.typicalLogDeviationSecondMoment n =
      (n : ℝ) * ρ.singleCopyLogDeviationSecondMoment := by
  -- The multiset-expansion identity is already established as
  -- `typicalLogDeviationSecondMoment_tensorPower`; here we bridge the `n = 1`
  -- tensor-power spectrum to the single-copy `Finset` definition.
  have hTensor := ρ.typicalLogDeviationSecondMoment_tensorPower n
  rw [hTensor]
  have h1 : ρ.typicalLogDeviationSecondMoment 1 = ρ.singleCopyLogDeviationSecondMoment := by
    rw [typicalLogDeviationSecondMoment_eq_multiset ρ 1,
        singleCopyLogDeviationSecondMoment_eq_multiset ρ,
        tensorPowerMultiset_one]
    simp only [Nat.cast_one, one_mul]
  rw [h1]

/-- The typical-subspace dimension satisfies the rate bound
`|T_δ^n| ≤ 2^{n(S(ρ)+δ)}`.

For each typical eigenvalue `μ`, the lower-bound equipartition (A) gives
`1 ≤ μ · 2^{n(S+δ)}`; summing over typical indices produces
`Σ 1 ≤ 2^{n(S+δ)} · typicalWeight ≤ 2^{n(S+δ)}`
[Wilde2011Qst, qit-notes.tex:31457-31598]. -/
theorem typicalSubspaceDimension_le_two_pow (ρ : State a) (n : ℕ) (δ : ℝ) :
    ρ.typicalSubspaceDimension n δ ≤ 2 ^ ((n : ℝ) * (ρ.vonNeumann + δ)) := by
  classical
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hfactor_pos : (0 : ℝ) < 2 ^ ((n : ℝ) * (ρ.vonNeumann + δ)) :=
    Real.rpow_pos_of_pos h2pos _
  have h0exp : -((n : ℝ) * ρ.vonNeumann + (n : ℝ) * δ) +
      (n : ℝ) * (ρ.vonNeumann + δ) = 0 := by ring
  have h1eq : (1 : ℝ) =
      2 ^ (-((n : ℝ) * ρ.vonNeumann + (n : ℝ) * δ)) *
        2 ^ ((n : ℝ) * (ρ.vonNeumann + δ)) := by
    rw [← Real.rpow_add h2pos, h0exp, Real.rpow_zero]
  unfold typicalSubspaceDimension
  calc
    (∑ i : TensorPower a n,
        if typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
        then (1 : ℝ) else 0)
      ≤ ∑ i : TensorPower a n,
          (if typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
            then ((ρ.tensorPower n).pos.isHermitian.eigenvalues i) *
              (2 ^ ((n : ℝ) * (ρ.vonNeumann + δ)))
            else (0 : ℝ)) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
        · simp only [hi, if_true]
          have hlower : 2 ^ (-((n : ℝ) * ρ.vonNeumann + (n : ℝ) * δ))
              ≤ (ρ.tensorPower n).pos.isHermitian.eigenvalues i :=
            ρ.typicalEigenvalue_ge_eigenvalueLowerBound n δ _ hi
          rw [h1eq]
          exact mul_le_mul_of_nonneg_right hlower hfactor_pos.le
        · simp only [hi, if_false, le_refl]
    _ = 2 ^ ((n : ℝ) * (ρ.vonNeumann + δ)) *
        ∑ i : TensorPower a n,
          (if typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
            then (ρ.tensorPower n).pos.isHermitian.eigenvalues i else (0 : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
        · simp only [hi, if_true]; ring
        · simp only [hi, if_false]; ring
    _ ≤ 2 ^ ((n : ℝ) * (ρ.vonNeumann + δ)) * 1 := by
        gcongr
        exact ρ.typicalSubspaceSpectralWeight_le_one n δ
    _ = 2 ^ ((n : ℝ) * (ρ.vonNeumann + δ)) := by ring

/-- The accepted spectral weight is bounded by the number of accepted spectral
directions times the typical eigenvalue upper envelope. -/
theorem typicalSubspaceSpectralWeight_le_dimension_mul_eigenvalueUpperBound
    (ρ : State a) (n : ℕ) (δ : ℝ) :
    ρ.typicalSubspaceSpectralWeight n δ ≤
      ρ.typicalSubspaceDimension n δ *
        2 ^ (-((n : ℝ) * ρ.vonNeumann - (n : ℝ) * δ)) := by
  classical
  let upper : ℝ := 2 ^ (-((n : ℝ) * ρ.vonNeumann - (n : ℝ) * δ))
  have hupper_nonneg : 0 ≤ upper := by
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  unfold typicalSubspaceSpectralWeight typicalSubspaceDimension
  calc
    (∑ i : TensorPower a n,
        if typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
        then (ρ.tensorPower n).pos.isHermitian.eigenvalues i else 0)
      ≤ ∑ i : TensorPower a n,
          (if typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
            then upper else 0) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : typicalEigenvalue ρ n δ
            ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
        · simp only [hi, if_true]
          exact ρ.typicalEigenvalue_le_eigenvalueUpperBound n δ _ hi
        · simp only [hi, if_false, le_refl]
    _ = (∑ i : TensorPower a n,
          if typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
          then (1 : ℝ) else 0) * upper := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : typicalEigenvalue ρ n δ
            ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
        · simp only [hi, if_true, one_mul]
        · simp only [hi, if_false, zero_mul]
    _ = (∑ i : TensorPower a n,
          if typicalEigenvalue ρ n δ ((ρ.tensorPower n).pos.isHermitian.eigenvalues i)
          then (1 : ℝ) else 0) *
        2 ^ (-((n : ℝ) * ρ.vonNeumann - (n : ℝ) * δ)) := by
        rfl

/-- Finite rank lower bound from accepted weight at least `1/2` and one bit of
exponent slack between the target rate window `δ` and the internal typicality
window `δ'`. -/
theorem two_pow_sub_le_typicalSubspaceDimension_of_half_le_spectralWeight
    (ρ : State a) {n : ℕ} {δ δ' : ℝ}
    (hweight : (1 / 2 : ℝ) ≤ ρ.typicalSubspaceSpectralWeight n δ')
    (hslack : 1 ≤ (n : ℝ) * (δ - δ')) :
    (2 : ℝ) ^ ((n : ℝ) * (ρ.vonNeumann - δ)) ≤
      ρ.typicalSubspaceDimension n δ' := by
  let lower : ℝ := (2 : ℝ) ^ ((n : ℝ) * (ρ.vonNeumann - δ))
  let upper : ℝ := (2 : ℝ) ^ (-((n : ℝ) * ρ.vonNeumann - (n : ℝ) * δ'))
  have hupper_pos : 0 < upper :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hweight_upper :
      ρ.typicalSubspaceSpectralWeight n δ' ≤
        ρ.typicalSubspaceDimension n δ' * upper :=
    ρ.typicalSubspaceSpectralWeight_le_dimension_mul_eigenvalueUpperBound n δ'
  have hhalf_le_dim_mul : (1 / 2 : ℝ) ≤ ρ.typicalSubspaceDimension n δ' * upper :=
    hweight.trans hweight_upper
  have hexponent_le :
      (n : ℝ) * (ρ.vonNeumann - δ) +
          (-((n : ℝ) * ρ.vonNeumann - (n : ℝ) * δ')) ≤ (-1 : ℝ) := by
    linarith
  have hprod_le_half : lower * upper ≤ (1 / 2 : ℝ) := by
    calc
      lower * upper =
          (2 : ℝ) ^ ((n : ℝ) * (ρ.vonNeumann - δ) +
            (-((n : ℝ) * ρ.vonNeumann - (n : ℝ) * δ'))) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexponent_le
      _ = (1 / 2 : ℝ) := by
          norm_num [Real.rpow_neg_one]
  have hmul : lower * upper ≤ ρ.typicalSubspaceDimension n δ' * upper :=
    hprod_le_half.trans hhalf_le_dim_mul
  exact le_of_mul_le_mul_right hmul hupper_pos

/-- The atypical spectral weight tends to zero as `n → ∞`.

Combines the Chebyshev bridge `atypical ≤ secondMoment / (nδ)²` with the exact
second-moment identity `secondMoment = n · singleCopy`, giving
`atypical ≤ singleCopy / (n · δ²) → 0` [Wilde2011Qst, qit-notes.tex:31457-31598]. -/
theorem tendsto_atypicalSubspaceSpectralWeight (ρ : State a) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => ρ.atypicalSubspaceSpectralWeight n δ) atTop (nhds 0) := by
  have hδ2pos : 0 < δ ^ 2 := sq_pos_of_pos hδ
  -- Chebyshev bound holds for `n ≥ 1`:
  --   `atypical n δ ≤ secondMoment n / (nδ)² = singleCopy / (n · δ²)`.
  have hBound : ∀ᶠ n in atTop,
      ρ.atypicalSubspaceSpectralWeight n δ ≤
        ρ.singleCopyLogDeviationSecondMoment / ((n : ℝ) * δ ^ 2) := by
    apply eventually_atTop.mpr
    refine ⟨1, fun n hn => ?_⟩
    have hn0 : 0 < n := by omega
    have hLin : ρ.typicalLogDeviationSecondMoment n =
        (n : ℝ) * ρ.singleCopyLogDeviationSecondMoment :=
      ρ.typicalLogDeviationSecondMoment_eq n
    have hCheb :=
      ρ.atypicalSubspaceSpectralWeight_le_logDeviationSecondMoment_div_sq hn0 hδ
    rw [hLin] at hCheb
    rw [show (n : ℝ) * ρ.singleCopyLogDeviationSecondMoment / ((n : ℝ) * δ) ^ 2 =
          ρ.singleCopyLogDeviationSecondMoment / ((n : ℝ) * δ ^ 2) by field_simp] at hCheb
    exact hCheb
  -- The bound itself tends to zero: `singleCopy / ((n:ℝ)·δ²) = (singleCopy/δ²)/n`.
  have hBoundTendsto :
      Tendsto (fun n : ℕ => ρ.singleCopyLogDeviationSecondMoment / ((n : ℝ) * δ ^ 2))
        atTop (nhds 0) := by
    have hCast : ∀ n : ℕ,
        (ρ.singleCopyLogDeviationSecondMoment / δ ^ 2) / (n : ℝ) =
          ρ.singleCopyLogDeviationSecondMoment / ((n : ℝ) * δ ^ 2) := by
      intro n; field_simp
    have hConst : Tendsto
        (fun n : ℕ => (ρ.singleCopyLogDeviationSecondMoment / δ ^ 2) / (n : ℝ))
        atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    exact Tendsto.congr' (Eventually.of_forall hCast) hConst
  -- Lower bound: `0 ≤ atypical` always.
  have hLower : ∀ᶠ n in atTop, (0 : ℝ) ≤ ρ.atypicalSubspaceSpectralWeight n δ :=
    Eventually.of_forall (fun n => ρ.atypicalSubspaceSpectralWeight_nonneg n δ)
  -- Squeeze: `0 ≤ atypical ≤ bound → 0`.
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) hBoundTendsto hLower hBound

/-- The typical spectral weight tends to one as `n → ∞`.

Follows from the partition `typical + atypical = 1` and
`tendsto_atypicalSubspaceSpectralWeight` [Wilde2011Qst, qit-notes.tex:31457-31598]. -/
theorem tendsto_typicalSubspaceSpectralWeight (ρ : State a) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => ρ.typicalSubspaceSpectralWeight n δ) atTop (nhds 1) := by
  -- `typical n δ = 1 - atypical n δ` via the partition identity.
  have hCast : (fun n : ℕ => ρ.typicalSubspaceSpectralWeight n δ) =
      fun n => 1 - ρ.atypicalSubspaceSpectralWeight n δ := by
    funext n
    linarith [ρ.typicalSubspaceSpectralWeight_add_atypical n δ]
  rw [hCast]
  simpa using tendsto_const_nhds.sub (ρ.tendsto_atypicalSubspaceSpectralWeight hδ)

/-- Eventually, the typical-subspace dimension dominates
`2^{n(S(ρ)-δ)}` when the caller supplies a smaller positive internal
typicality window `δ' < δ`. -/
theorem eventually_two_pow_sub_le_typicalSubspaceDimension
    (ρ : State a) {δ δ' : ℝ} (hδ' : 0 < δ') (hslack : δ' < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      (2 : ℝ) ^ ((n : ℝ) * (ρ.vonNeumann - δ)) ≤
        ρ.typicalSubspaceDimension n δ' := by
  have hhalf_eventually :
      ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ≤ ρ.typicalSubspaceSpectralWeight n δ' := by
    have hgt :
        ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) < ρ.typicalSubspaceSpectralWeight n δ' :=
      (ρ.tendsto_typicalSubspaceSpectralWeight hδ').eventually
        (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
    exact hgt.mono fun _ hn => hn.le
  have hgap_pos : 0 < δ - δ' := sub_pos.mpr hslack
  have hslack_eventually :
      ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) * (δ - δ') := by
    apply eventually_atTop.mpr
    refine ⟨Nat.ceil (1 / (δ - δ')), fun n hn => ?_⟩
    have hceil : 1 / (δ - δ') ≤ (Nat.ceil (1 / (δ - δ')) : ℝ) :=
      Nat.le_ceil _
    have hnR : (Nat.ceil (1 / (δ - δ')) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hone_div_le_n : 1 / (δ - δ') ≤ (n : ℝ) := hceil.trans hnR
    have hmul := mul_le_mul_of_nonneg_right hone_div_le_n hgap_pos.le
    have hcancel : (1 / (δ - δ')) * (δ - δ') = 1 := by
      field_simp [ne_of_gt hgap_pos]
    linarith
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        (2 : ℝ) ^ ((n : ℝ) * (ρ.vonNeumann - δ)) ≤
          ρ.typicalSubspaceDimension n δ' := by
    filter_upwards [hhalf_eventually, hslack_eventually] with n hweight hnslack
    exact ρ.two_pow_sub_le_typicalSubspaceDimension_of_half_le_spectralWeight
      hweight hnslack
  exact Filter.eventually_atTop.mp hevent

end State

end

end QIT
