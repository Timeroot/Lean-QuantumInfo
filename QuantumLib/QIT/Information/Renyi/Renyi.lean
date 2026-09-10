/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Entropy.Entropy
public import QuantumLib.QIT.Information.Entropy.Log2Lemmas
public import QuantumLib.QIT.Classical.Bridge
public import QuantumLib.QIT.States.Schatten
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Quantum Renyi divergences

Petz and sandwiched Renyi divergences defined via `CFC.rpow`, plus their
tensor-power additivity under `MState.prod` (Kronecker product). This is the
FQAEP engine layer — the Renyi family is the workhorse of the finite-N AEP
and one-shot decoupling bounds.

The definitions expose positive-definite input witnesses and order-domain
witnesses `0 < α`, `α ≠ 1` as API preconditions. The witnesses are not
computationally used by `CFC.rpow`, but they keep downstream theorem
statements aligned with the mathematical domain.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

open Matrix Polynomial

noncomputable section
universe u v
variable {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

open QIT

namespace QIT

/-- Relabeling the index type of a complex matrix by `M ↦ M.submatrix e e` is a
star-algebra isomorphism. -/
def cMatrixSubmatrixStarAlgEquiv
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) : CMatrix κ ≃⋆ₐ[ℂ] CMatrix ι where
  __ := Matrix.reindexAlgEquiv ℂ ℂ e.symm
  map_smul' r M := by
    ext i j
    simp [Matrix.reindex_apply]
  map_star' M := by
    ext i j
    simp [Matrix.reindex_apply]

/-- Relabeling the index type of a complex matrix by `Matrix.reindex e e` is a
star-algebra isomorphism. -/
noncomputable def cMatrixReindexStarAlgEquiv
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) : CMatrix ι ≃⋆ₐ[ℂ] CMatrix κ where
  __ := Matrix.reindexAlgEquiv ℂ ℂ e
  map_smul' r A := by
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  map_star' A := by
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]

/-- Real powers commute with finite basis relabeling for positive-definite
complex matrices, for every real exponent. -/
theorem cMatrix_rpow_submatrix_equiv_posDef
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : CMatrix κ) (hM : M.PosDef) (e : ι ≃ κ) (s : ℝ) :
    CFC.rpow (M.submatrix e e) s = (CFC.rpow M s).submatrix e e := by
  change (M.submatrix e e) ^ s = (M ^ s).submatrix e e
  have hsub_nonneg : 0 ≤ M.submatrix e e :=
    Matrix.nonneg_iff_posSemidef.mpr (hM.posSemidef.submatrix e)
  have hM_nonneg : 0 ≤ M :=
    Matrix.nonneg_iff_posSemidef.mpr hM.posSemidef
  rw [CFC.rpow_eq_cfc_real (a := M.submatrix e e) (y := s) hsub_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := M) (y := s) hM_nonneg]
  exact
    (StarAlgHomClass.map_cfc
      (cMatrixSubmatrixStarAlgEquiv e)
      (fun x : ℝ => x ^ s) M
      (hf := by
        intro x hx
        exact (Real.continuousAt_rpow_const x s
          (.inl (ne_of_gt ((Matrix.PosDef.isStrictlyPositive hM).spectrum_pos hx)))).continuousWithinAt)
      (hφ := by
        change Continuous fun A : CMatrix κ => A.submatrix e e
        fun_prop)).symm

/-- Nonnegative real powers commute with finite basis relabeling for positive
semidefinite complex matrices. -/
theorem cMatrix_rpow_submatrix_equiv_nonneg
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : CMatrix κ) (hM : M.PosSemidef) (e : ι ≃ κ)
    {s : ℝ} (hs0 : 0 ≤ s) :
    CFC.rpow (M.submatrix e e) s = (CFC.rpow M s).submatrix e e := by
  change (M.submatrix e e) ^ s = (M ^ s).submatrix e e
  have hsub_nonneg : 0 ≤ M.submatrix e e :=
    Matrix.nonneg_iff_posSemidef.mpr (hM.submatrix e)
  have hM_nonneg : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM
  rw [CFC.rpow_eq_cfc_real (a := M.submatrix e e) (y := s) hsub_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := M) (y := s) hM_nonneg]
  simpa [cMatrixSubmatrixStarAlgEquiv, Matrix.coe_reindexAlgEquiv] using
    (StarAlgHomClass.map_cfc
      (cMatrixSubmatrixStarAlgEquiv e)
      (fun x : ℝ => x ^ s) M
      (hf := (Real.continuous_rpow_const hs0).continuousOn)
      (hφ := by
        change Continuous fun A : CMatrix κ => A.submatrix e e
        fun_prop)).symm

theorem trace_mul_posSemidef_im_eq_zero {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ((A * B).trace).im = 0 := by
  let S := psdSqrt A
  have hpsd : (S * B * S).PosSemidef := by
    have h := hB.mul_mul_conjTranspose_same S
    dsimp [S] at h
    rw [psdSqrt_isHermitian A] at h
    exact h
  have htrace : 0 ≤ (S * B * S).trace :=
    Matrix.PosSemidef.trace_nonneg hpsd
  have hEq : (A * B).trace = (S * B * S).trace := by
    have hsqrt : S * S = A := by
      simpa [S] using psdSqrt_mul_self_of_posSemidef hA
    rw [← hsqrt]
    calc
      ((S * S) * B).trace = (S * (S * B)).trace := by
        rw [Matrix.mul_assoc]
      _ = ((S * B) * S).trace := by
        rw [Matrix.trace_mul_comm]
      _ = (S * B * S).trace := by
        rw [Matrix.mul_assoc]
  rw [hEq]
  exact htrace.2.symm

/-- A binary measurement of a positive semidefinite matrix is the real diagonal
matrix of its Born-rule weights. -/
theorem measurement_map_eq_diagonal_re (M : POVM Bool a)
    {X : CMatrix a} (hX : X.PosSemidef) :
    (POVM.measureDiscard M).map X =
      (Matrix.diagonal fun b : Bool => (((X * M.effects b).trace).re : ℂ)) := by
  ext i j
  cases i <;> cases j
  all_goals simp [POVM.measureDiscard_map, Matrix.diagonal]
  all_goals
    apply Complex.ext <;>
      simp [trace_mul_posSemidef_im_eq_zero hX (M.pos false),
        trace_mul_posSemidef_im_eq_zero hX (M.pos true)]

/-- The trace of the product of two positive definite matrices is positive. -/
theorem trace_mul_posDef_re_pos {A B : CMatrix a} [Nonempty a]
    (hA : A.PosDef) (hB : B.PosDef) :
    0 < ((A * B).trace).re := by
  let S := psdSqrt A
  have hS_hm : S.IsHermitian := psdSqrt_isHermitian A
  have hS_posdef : S.PosDef := by
    rw [show S = CFC.rpow A (1 / 2 : ℝ) by
      simp [S, psdSqrt, CFC.sqrt_eq_rpow]]
    change (A ^ (1 / 2 : ℝ)).PosDef
    rw [CFC.rpow_eq_cfc_real (a := A) (y := (1 / 2 : ℝ))
      (Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef)]
    rw [hA.isHermitian.cfc_eq]
    rw [Matrix.IsHermitian.cfc]
    simp only [Unitary.conjStarAlgAut_apply]
    rw [Matrix.IsUnit.posDef_star_right_conjugate_iff (Unitary.isUnit_coe :
      IsUnit (hA.isHermitian.eigenvectorUnitary : CMatrix a))]
    rw [Matrix.posDef_diagonal_iff]
    intro i
    have hr : 0 < hA.isHermitian.eigenvalues i ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos (hA.eigenvalues_pos i) (1 / 2 : ℝ)
    show 0 < ((hA.isHermitian.eigenvalues i ^ (1 / 2 : ℝ) : ℝ) : ℂ)
    exact_mod_cast hr
  have hpsd : (S * B * S).PosDef := by
    have h := hB.mul_mul_conjTranspose_same (B := S) ?_
    · rwa [hS_hm.eq] at h
    · exact Matrix.vecMul_injective_of_isUnit hS_posdef.isUnit
  have hEq : (A * B).trace = (S * B * S).trace := by
    have hsqrt : S * S = A := by
      simpa [S] using psdSqrt_mul_self_of_posSemidef hA.posSemidef
    rw [← hsqrt]
    calc
      ((S * S) * B).trace = (S * (S * B)).trace := by
        rw [Matrix.mul_assoc]
      _ = ((S * B) * S).trace := by
        rw [Matrix.trace_mul_comm]
      _ = (S * B * S).trace := by
        rw [Matrix.mul_assoc]
  rw [hEq]
  exact (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hpsd)).1

private theorem renyi_cMatrix_rpow_posSemidef (A : CMatrix a) (s : ℝ) :
    (CFC.rpow A s).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := A) (y := s))

theorem cMatrix_rpow_posDef_of_posDef {A : CMatrix a} (hA : A.PosDef) (s : ℝ) :
    (CFC.rpow A s).PosDef := by
  change (A ^ s).PosDef
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s)
    (Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef)]
  rw [hA.isHermitian.cfc_eq]
  rw [Matrix.IsHermitian.cfc]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [Matrix.IsUnit.posDef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (hA.isHermitian.eigenvectorUnitary : CMatrix a))]
  rw [Matrix.posDef_diagonal_iff]
  intro i
  have hr : 0 < hA.isHermitian.eigenvalues i ^ s :=
    Real.rpow_pos_of_pos (hA.eigenvalues_pos i) s
  show 0 < ((hA.isHermitian.eigenvalues i ^ s : ℝ) : ℂ)
  exact_mod_cast hr

namespace Classical

/-- A strictly positive classical probability vector gives a positive-definite
diagonal state. -/
theorem diagonalState_posDef (p : a → ℝ≥0) (hsum : ∑ i, p i = 1)
    (hp : ∀ i, 0 < (p i : ℝ)) :
    (diagonalState p hsum).m.PosDef := by
  rw [diagonalState_matrix, Matrix.posDef_diagonal_iff]
  intro i
  change 0 < ((p i : ℂ))
  exact_mod_cast hp i

end Classical

end QIT

namespace MState

/-- Unitary conjugation of a density state. -/
def unitaryConj (ρ : MState a) (U : Matrix.unitaryGroup a ℂ) : MState a := .ofMatrix
  (matrix := (U : CMatrix a) * ρ.m * star (U : CMatrix a))
  (pos := by
    simpa [Matrix.star_eq_conjTranspose] using
      ρ.psd.mul_mul_conjTranspose_same (U : CMatrix a))
  (trace_eq_one := by
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul, ρ.tr'])

@[simp]
theorem unitaryConj_matrix (ρ : MState a) (U : Matrix.unitaryGroup a ℂ) :
    (ρ.unitaryConj U).m = (U : CMatrix a) * ρ.m * star (U : CMatrix a) :=
  MState.matrix_ofMatrix _ _ _

/-- Positive definiteness is preserved by unitary conjugation. -/
theorem unitaryConj_posDef (ρ : MState a) (U : Matrix.unitaryGroup a ℂ)
    (hρ : ρ.m.PosDef) :
    (ρ.unitaryConj U).m.PosDef := by
  rw [unitaryConj_matrix]
  rw [Matrix.IsUnit.posDef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (U : CMatrix a))]
  exact hρ

/-- Petz quantum Renyi divergence D_α(ρ‖σ) = 1/(α-1) · log2 Tr(ρ^α · σ^(1-α)).

Requires α > 0, α ≠ 1 and both states positive-definite (invertible). -/
def petzRenyi (ρ σ : MState a) (_hρ : ρ.m.PosDef) (_hσ : σ.m.PosDef)
    (α : ℝ) (_hα_pos : 0 < α) (_hα_ne_one : α ≠ 1) : ℝ :=
  let r := 1 / (α - 1)
  let A := CFC.rpow ρ.m α
  let B := CFC.rpow σ.m (1 - α)
  r * log2 ((A * B).trace.re)

/-- Petz quantum Renyi divergence in the PSD branch used for `0 < α < 1`.

For this order range no inverse power of the second state is needed.  This
definition is the source-faithful kernel for Khatri--Wilde's
`D_α(ρ ‖ σ)` comparison with a merely positive semidefinite `σ`. -/
def petzRenyiPSDFinite (ρ σ : MState a)
    (α : ℝ) (_hα_pos : 0 < α) (_hα_ne_one : α ≠ 1) : ℝ :=
  let r := 1 / (α - 1)
  let A := CFC.rpow ρ.m α
  let B := CFC.rpow σ.m (1 - α)
  r * log2 ((A * B).trace.re)

/-- Petz trace coefficient in the PSD order range. -/
def petzRenyiPSDTraceCoeff (ρ σ : MState a) (α : ℝ) : ℝ :=
  ((CFC.rpow ρ.m α * CFC.rpow σ.m (1 - α)).trace).re

/-- The Petz trace coefficient is nonnegative for density operators. -/
theorem petzRenyiPSDTraceCoeff_nonneg
    (ρ σ : MState a) (α : ℝ) :
    0 ≤ ρ.petzRenyiPSDTraceCoeff σ α := by
  exact cMatrix_trace_mul_posSemidef_re_nonneg
    (renyi_cMatrix_rpow_posSemidef ρ.m α)
    (renyi_cMatrix_rpow_posSemidef σ.m (1 - α))

/-- Powered support inclusion makes the PSD Petz trace coefficient positive. -/
theorem petzRenyiPSDTraceCoeff_pos_of_support
    (ρ σ : MState a) {α : ℝ}
    (hSupport : Matrix.Supports (CFC.rpow ρ.m α) σ.m) :
    0 < ρ.petzRenyiPSDTraceCoeff σ α := by
  have hMne : CFC.rpow ρ.m α ≠ 0 := by
    have hρne : ρ.m ≠ 0 := by
      intro hzero
      have htrace := ρ.tr'
      rw [hzero] at htrace
      simp at htrace
    have hpow_pos := psdTracePower_pos_of_ne_zero ρ.m ρ.psd (p := α) hρne
    intro hzero
    have hpow_zero : psdTracePower ρ.m ρ.psd α = 0 := by
      change (CFC.rpow ρ.m α).trace.re = 0
      rw [hzero]
      simp
    linarith
  exact trace_mul_cMatrix_rpow_pos_of_support
    (M := CFC.rpow ρ.m α) (N := σ.m)
    (cMatrix_rpow_posSemidef (A := ρ.m) (s := α) ρ.psd) σ.psd
    hMne hSupport (1 - α)

/-- Canonical extended-real Petz divergence for PSD states and `0 < α < 1`.

If the Petz trace coefficient vanishes, the negative prefactor multiplies the
logarithmic singularity to `+∞`.  Otherwise this agrees with the finite real
formula. -/
noncomputable def petzRenyiPSD (ρ σ : MState a)
    (α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1) : EReal :=
  if ρ.petzRenyiPSDTraceCoeff σ α = 0 then
    ⊤
  else
    (ρ.petzRenyiPSDFinite σ α hα_pos (ne_of_lt hα_lt_one) : EReal)

theorem petzRenyiPSD_eq_top_of_traceCoeff_eq_zero
    (ρ σ : MState a) (α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hzero : ρ.petzRenyiPSDTraceCoeff σ α = 0) :
    ρ.petzRenyiPSD σ α hα_pos hα_lt_one = (⊤ : EReal) := by
  simp [petzRenyiPSD, hzero]

theorem petzRenyiPSD_eq_coe_finite_of_traceCoeff_ne_zero
    (ρ σ : MState a) (α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hne : ρ.petzRenyiPSDTraceCoeff σ α ≠ 0) :
    ρ.petzRenyiPSD σ α hα_pos hα_lt_one =
      (ρ.petzRenyiPSDFinite σ α hα_pos (ne_of_lt hα_lt_one) : EReal) := by
  simp [petzRenyiPSD, hne]

/-- A positive Petz trace coefficient selects the finite branch of the
canonical PSD divergence. -/
theorem petzRenyiPSD_eq_coe_finite_of_traceCoeff_pos
    (ρ σ : MState a) (α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hpos : 0 < ρ.petzRenyiPSDTraceCoeff σ α) :
    ρ.petzRenyiPSD σ α hα_pos hα_lt_one =
      (ρ.petzRenyiPSDFinite σ α hα_pos (ne_of_lt hα_lt_one) : EReal) :=
  ρ.petzRenyiPSD_eq_coe_finite_of_traceCoeff_ne_zero
    σ α hα_pos hα_lt_one (ne_of_gt hpos)

theorem petzRenyiPSDFinite_eq_petzRenyi
    (ρ σ : MState a) (hρ : ρ.m.PosDef) (hσ : σ.m.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.petzRenyiPSDFinite σ α hα_pos hα_ne_one =
      ρ.petzRenyi σ hρ hσ α hα_pos hα_ne_one := rfl

/-- On positive-definite states, the canonical PSD API is the coercion of the
ordinary finite Petz divergence. -/
theorem petzRenyiPSD_eq_coe_petzRenyi_of_posDef
    (ρ σ : MState a) (hρ : ρ.m.PosDef) (hσ : σ.m.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    ρ.petzRenyiPSD σ α hα_pos hα_lt_one =
      (ρ.petzRenyi σ hρ hσ α hα_pos (ne_of_lt hα_lt_one) : EReal) := by
  have : Nonempty a := ρ.nonempty
  have hcoeff_pos : 0 < ρ.petzRenyiPSDTraceCoeff σ α := by
    exact trace_mul_posDef_re_pos
      (cMatrix_rpow_posDef_of_posDef hρ α)
      (cMatrix_rpow_posDef_of_posDef hσ (1 - α))
  rw [ρ.petzRenyiPSD_eq_coe_finite_of_traceCoeff_ne_zero
    σ α hα_pos hα_lt_one (ne_of_gt hcoeff_pos)]
  rw [ρ.petzRenyiPSDFinite_eq_petzRenyi
    σ hρ hσ α hα_pos (ne_of_lt hα_lt_one)]

/-- Sandwiched quantum Renyi divergence D̃_α(ρ‖σ).

D̃_α(ρ‖σ) = 1/(α-1) · log2 Tr((σ^((1-α)/2α) · ρ · σ^((1-α)/2α))^α). -/
def sandwichedRenyi (ρ σ : MState a) (_hρ : ρ.m.PosDef) (_hσ : σ.m.PosDef)
    (α : ℝ) (_hα_pos : 0 < α) (_hα_ne_one : α ≠ 1) : ℝ :=
  let r := 1 / (α - 1)
  let s := (1 - α) / (2 * α)
  let C := CFC.rpow σ.m s
  let M := CFC.rpow (C * ρ.m * C) α
  r * log2 (M.trace.re)

/-- Sandwiched Renyi divergence against a positive-definite reference operator.

This is the non-normalized-reference companion to `sandwichedRenyi`: the first
argument remains a normalized state, while the reference is a positive-definite
matrix.  It is the local entry point for the source formulation in which the
second argument is a PSD reference operator rather than a density state. -/
def sandwichedRenyiReference
    (ρ : MState a) (σ : CMatrix a) (_hρ : ρ.m.PosDef) (_hσ : σ.PosDef)
    (α : ℝ) (_hα_pos : 0 < α) (_hα_ne_one : α ≠ 1) : ℝ :=
  let r := 1 / (α - 1)
  let s := (1 - α) / (2 * α)
  let C := CFC.rpow σ s
  let M := CFC.rpow (C * ρ.m * C) α
  r * log2 (M.trace.re)

/-- The matrix-reference version agrees definitionally with the normalized-state
version when the reference matrix comes from a `MState`. -/
theorem sandwichedRenyiReference_state
    (ρ σ : MState a) (hρ : ρ.m.PosDef) (hσ : σ.m.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyiReference ρ σ.m hρ hσ α hα_pos hα_ne_one =
      sandwichedRenyi ρ σ hρ hσ α hα_pos hα_ne_one := by
  rfl

/-- Normalize a positive-definite reference matrix into a density state. -/
def stateOfPosDefReference [Nonempty a] (σ : CMatrix a) (hσ : σ.PosDef) : MState a := .ofMatrix
  (matrix := (σ.trace.re)⁻¹ • σ)
  (pos := by
    have htr_pos : 0 < σ.trace.re :=
      (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hσ)).1
    exact Matrix.PosSemidef.smul hσ.posSemidef
      (inv_nonneg.mpr (le_of_lt htr_pos)))
  (trace_eq_one := by
    have htr_pos : 0 < σ.trace.re :=
      (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hσ)).1
    have htr_im : σ.trace.im = 0 :=
      (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hσ)).2.symm
    rw [Matrix.trace_smul]
    apply Complex.ext
    · simp [Complex.real_smul, ne_of_gt htr_pos]
    · simp [Complex.real_smul, htr_im])

@[simp]
theorem stateOfPosDefReference_matrix [Nonempty a] (σ : CMatrix a) (hσ : σ.PosDef) :
    (stateOfPosDefReference σ hσ).m = (σ.trace.re)⁻¹ • σ :=
  MState.matrix_ofMatrix _ _ _

/-- The normalized state associated to a positive-definite reference remains
positive definite. -/
theorem stateOfPosDefReference_posDef [Nonempty a] (σ : CMatrix a)
    (hσ : σ.PosDef) :
    (stateOfPosDefReference σ hσ).m.PosDef := by
  have htr_pos : 0 < σ.trace.re :=
    (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hσ)).1
  simpa [stateOfPosDefReference] using Matrix.PosDef.smul hσ (inv_pos.mpr htr_pos)

/-- Petz Renyi divergence is invariant under applying the same unitary
conjugation to both arguments. -/
theorem petzRenyi_unitaryConj
    (ρ σ : MState a) (U : Matrix.unitaryGroup a ℂ)
    (hρ : ρ.m.PosDef) (hσ : σ.m.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    petzRenyi (ρ.unitaryConj U) (σ.unitaryConj U)
        (ρ.unitaryConj_posDef U hρ) (σ.unitaryConj_posDef U hσ)
        α hα_pos hα_ne_one =
      petzRenyi ρ σ hρ hσ α hα_pos hα_ne_one := by
  let A : CMatrix a := CFC.rpow ρ.m α
  let B : CMatrix a := CFC.rpow σ.m (1 - α)
  have hρpow :
      CFC.rpow (ρ.unitaryConj U).m α =
        (U : CMatrix a) * A * star (U : CMatrix a) := by
    simpa [A, unitaryConj, Unitary.conjStarAlgAut_apply] using
      cMatrix_rpow_conjStarAlgAut_posDef U hρ α
  have hσpow :
      CFC.rpow (σ.unitaryConj U).m (1 - α) =
        (U : CMatrix a) * B * star (U : CMatrix a) := by
    simpa [B, unitaryConj, Unitary.conjStarAlgAut_apply] using
      cMatrix_rpow_conjStarAlgAut_posDef U hσ (1 - α)
  have htrace :
      ((CFC.rpow (ρ.unitaryConj U).m α *
          CFC.rpow (σ.unitaryConj U).m (1 - α)).trace).re =
        ((A * B).trace).re := by
    rw [hρpow, hσpow]
    have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
      Unitary.coe_star_mul_self U
    have hprod :
        ((U : CMatrix a) * A * star (U : CMatrix a)) *
            ((U : CMatrix a) * B * star (U : CMatrix a)) =
          (U : CMatrix a) * (A * B) * star (U : CMatrix a) := by
      calc
        ((U : CMatrix a) * A * star (U : CMatrix a)) *
            ((U : CMatrix a) * B * star (U : CMatrix a)) =
            (U : CMatrix a) * A * (star (U : CMatrix a) * (U : CMatrix a)) *
              B * star (U : CMatrix a) := by
              noncomm_ring
        _ = (U : CMatrix a) * A * 1 * B * star (U : CMatrix a) := by
              rw [hUstarU]
        _ = (U : CMatrix a) * (A * B) * star (U : CMatrix a) := by
              noncomm_ring
    rw [hprod]
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
  unfold petzRenyi
  change
    (1 / (α - 1)) *
        log2
          ((CFC.rpow (ρ.unitaryConj U).m α *
            CFC.rpow (σ.unitaryConj U).m (1 - α)).trace).re =
      (1 / (α - 1)) * log2 ((A * B).trace).re
  rw [htrace]

/-- Sandwiched Renyi divergence is invariant under applying the same unitary
conjugation to both arguments. -/
theorem sandwichedRenyi_unitaryConj
    (ρ σ : MState a) (U : Matrix.unitaryGroup a ℂ)
    (hρ : ρ.m.PosDef) (hσ : σ.m.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyi (ρ.unitaryConj U) (σ.unitaryConj U)
        (ρ.unitaryConj_posDef U hρ) (σ.unitaryConj_posDef U hσ)
        α hα_pos hα_ne_one =
      sandwichedRenyi ρ σ hρ hσ α hα_pos hα_ne_one := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ.m s
  let inner : CMatrix a := C * ρ.m * C
  have hσpow :
      CFC.rpow (σ.unitaryConj U).m s =
        (U : CMatrix a) * C * star (U : CMatrix a) := by
    simpa [C, unitaryConj, Unitary.conjStarAlgAut_apply] using
      cMatrix_rpow_conjStarAlgAut_posDef U hσ s
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
    Unitary.coe_star_mul_self U
  have hinner :
      CFC.rpow (σ.unitaryConj U).m s *
          (ρ.unitaryConj U).m *
          CFC.rpow (σ.unitaryConj U).m s =
        (U : CMatrix a) * inner * star (U : CMatrix a) := by
    rw [hσpow, unitaryConj_matrix]
    calc
      ((U : CMatrix a) * C * star (U : CMatrix a)) *
          ((U : CMatrix a) * ρ.m * star (U : CMatrix a)) *
          ((U : CMatrix a) * C * star (U : CMatrix a)) =
          (U : CMatrix a) * C * (star (U : CMatrix a) * (U : CMatrix a)) *
            ρ.m * (star (U : CMatrix a) * (U : CMatrix a)) *
            C * star (U : CMatrix a) := by
            noncomm_ring
      _ = (U : CMatrix a) * C * 1 * ρ.m * 1 *
            C * star (U : CMatrix a) := by
            rw [hUstarU]
      _ = (U : CMatrix a) * inner * star (U : CMatrix a) := by
            simp [inner, Matrix.mul_assoc]
  have hC_pos : C.PosDef :=
    cMatrix_rpow_posDef_of_posDef hσ s
  have hC_hm : C.IsHermitian :=
    (renyi_cMatrix_rpow_posSemidef σ.m s).isHermitian
  have hinner_pos : inner.PosDef := by
    have h := hρ.mul_mul_conjTranspose_same (B := C) ?_
    · simpa [inner] using (show C * ρ.m * C = inner by rfl ▸ (by rwa [hC_hm.eq] at h))
    · exact Matrix.vecMul_injective_of_isUnit hC_pos.isUnit
  have hMpow :
      CFC.rpow
          (CFC.rpow (σ.unitaryConj U).m s *
            (ρ.unitaryConj U).m *
            CFC.rpow (σ.unitaryConj U).m s) α =
        (U : CMatrix a) * CFC.rpow inner α * star (U : CMatrix a) := by
    rw [hinner]
    simpa [Unitary.conjStarAlgAut_apply] using
      cMatrix_rpow_conjStarAlgAut_posDef U hinner_pos α
  have htrace :
      (CFC.rpow
          (CFC.rpow (σ.unitaryConj U).m s *
            (ρ.unitaryConj U).m *
            CFC.rpow (σ.unitaryConj U).m s) α).trace.re =
        (CFC.rpow inner α).trace.re := by
    rw [hMpow]
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
  unfold sandwichedRenyi
  change
    (1 / (α - 1)) *
        log2
          (CFC.rpow
            (CFC.rpow (σ.unitaryConj U).m s *
              (ρ.unitaryConj U).m *
              CFC.rpow (σ.unitaryConj U).m s) α).trace.re =
      (1 / (α - 1)) * log2 (CFC.rpow inner α).trace.re
  rw [htrace]

/-- Classical diagonal full-rank states reduce the Petz Renyi divergence to the
usual finite classical Renyi power sum. -/
theorem petzRenyi_diagonalState_eq_classicalPowerSum
    (p q : a → ℝ≥0) (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hp_pos : ∀ i, 0 < (p i : ℝ)) (hq_pos : ∀ i, 0 < (q i : ℝ))
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    petzRenyi (Classical.diagonalState p hp_sum) (Classical.diagonalState q hq_sum)
        (Classical.diagonalState_posDef p hp_sum hp_pos)
        (Classical.diagonalState_posDef q hq_sum hq_pos)
        α hα_pos hα_ne_one =
      (1 / (α - 1)) *
        log2 (∑ i, ((p i : ℝ) ^ α) * ((q i : ℝ) ^ (1 - α))) := by
  have hp_nonneg : ∀ i, 0 ≤ (p i : ℝ) := fun i => le_of_lt (hp_pos i)
  have hq_nonneg : ∀ i, 0 ≤ (q i : ℝ) := fun i => le_of_lt (hq_pos i)
  have hρpow :
      CFC.rpow (Classical.diagonalState p hp_sum).m α =
        Matrix.diagonal (fun i => (((p i : ℝ) ^ α : ℝ) : ℂ)) := by
    rw [Classical.diagonalState_matrix]
    exact cMatrix_rpow_diagonal_ofReal (fun i => (p i : ℝ)) hp_nonneg α
  have hσpow :
      CFC.rpow (Classical.diagonalState q hq_sum).m (1 - α) =
        Matrix.diagonal (fun i => (((q i : ℝ) ^ (1 - α) : ℝ) : ℂ)) := by
    rw [Classical.diagonalState_matrix]
    exact cMatrix_rpow_diagonal_ofReal (fun i => (q i : ℝ)) hq_nonneg (1 - α)
  have htrace :
      ((CFC.rpow (Classical.diagonalState p hp_sum).m α *
        CFC.rpow (Classical.diagonalState q hq_sum).m (1 - α)).trace).re =
        ∑ i, ((p i : ℝ) ^ α) * ((q i : ℝ) ^ (1 - α)) := by
    rw [hρpow, hσpow, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    simp
  unfold petzRenyi
  change
    (1 / (α - 1)) *
        log2
          ((CFC.rpow (Classical.diagonalState p hp_sum).m α *
            CFC.rpow (Classical.diagonalState q hq_sum).m (1 - α)).trace).re =
      (1 / (α - 1)) *
        log2 (∑ i, ((p i : ℝ) ^ α) * ((q i : ℝ) ^ (1 - α)))
  rw [htrace]

private theorem diagonal_sandwiched_power_term (p q α : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hα : 0 < α) :
    (q ^ ((1 - α) / (2 * α)) * p * q ^ ((1 - α) / (2 * α))) ^ α =
      p ^ α * q ^ (1 - α) := by
  let s : ℝ := (1 - α) / (2 * α)
  have hp_nonneg : 0 ≤ p := le_of_lt hp
  have hq_nonneg : 0 ≤ q := le_of_lt hq
  have hqs_nonneg : 0 ≤ q ^ s := Real.rpow_nonneg hq_nonneg s
  have hsα : (s + s) * α = 1 - α := by
    dsimp [s]
    field_simp [ne_of_gt hα]
    ring
  calc
    (q ^ ((1 - α) / (2 * α)) * p * q ^ ((1 - α) / (2 * α))) ^ α =
        (p * (q ^ s * q ^ s)) ^ α := by
          dsimp [s]
          ring_nf
    _ = p ^ α * (q ^ s * q ^ s) ^ α := by
          rw [Real.mul_rpow hp_nonneg (mul_nonneg hqs_nonneg hqs_nonneg)]
    _ = p ^ α * (q ^ (s + s)) ^ α := by
          rw [Real.rpow_add hq s s]
    _ = p ^ α * q ^ ((s + s) * α) := by
          rw [← Real.rpow_mul hq_nonneg (s + s) α]
    _ = p ^ α * q ^ (1 - α) := by
          rw [hsα]

/-- Classical diagonal full-rank states reduce the sandwiched Renyi divergence
to the usual classical Renyi power sum.

This is the commuting endpoint needed by the sandwiched-Renyi pinching route:
after a pinching/classical reduction, the noncommutative expression must land on
this finite power-sum formula. -/
theorem sandwichedRenyi_diagonalState_eq_classicalPowerSum
    (p q : a → ℝ≥0) (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hp_pos : ∀ i, 0 < (p i : ℝ)) (hq_pos : ∀ i, 0 < (q i : ℝ))
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyi (Classical.diagonalState p hp_sum) (Classical.diagonalState q hq_sum)
        (Classical.diagonalState_posDef p hp_sum hp_pos)
        (Classical.diagonalState_posDef q hq_sum hq_pos)
        α hα_pos hα_ne_one =
      (1 / (α - 1)) *
        log2 (∑ i, ((p i : ℝ) ^ α) * ((q i : ℝ) ^ (1 - α))) := by
  let s : ℝ := (1 - α) / (2 * α)
  have hp_nonneg : ∀ i, 0 ≤ (p i : ℝ) := fun i => le_of_lt (hp_pos i)
  have hq_nonneg : ∀ i, 0 ≤ (q i : ℝ) := fun i => le_of_lt (hq_pos i)
  have hC :
      CFC.rpow (Classical.diagonalState q hq_sum).m s =
        Matrix.diagonal (fun i => (((q i : ℝ) ^ s : ℝ) : ℂ)) := by
    rw [Classical.diagonalState_matrix]
    exact cMatrix_rpow_diagonal_ofReal (fun i => (q i : ℝ)) hq_nonneg s
  have hinner :
      CFC.rpow (Classical.diagonalState q hq_sum).m s *
          (Classical.diagonalState p hp_sum).m *
          CFC.rpow (Classical.diagonalState q hq_sum).m s =
        Matrix.diagonal
          (fun i => ((((q i : ℝ) ^ s) * (p i : ℝ) * ((q i : ℝ) ^ s) : ℝ) : ℂ)) := by
    rw [hC, Classical.diagonalState_matrix, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [mul_assoc]
    · simp [Matrix.diagonal, hij]
  have hinner_nonneg :
      ∀ i, 0 ≤ ((q i : ℝ) ^ s * (p i : ℝ) * (q i : ℝ) ^ s) := by
    intro i
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (hq_nonneg i) s) (hp_nonneg i))
      (Real.rpow_nonneg (hq_nonneg i) s)
  have hM :
      CFC.rpow
          (CFC.rpow (Classical.diagonalState q hq_sum).m s *
            (Classical.diagonalState p hp_sum).m *
            CFC.rpow (Classical.diagonalState q hq_sum).m s) α =
        Matrix.diagonal
          (fun i =>
            ((((q i : ℝ) ^ s * (p i : ℝ) * (q i : ℝ) ^ s) ^ α : ℝ) : ℂ)) := by
    rw [hinner]
    exact cMatrix_rpow_diagonal_ofReal
      (fun i => (q i : ℝ) ^ s * (p i : ℝ) * (q i : ℝ) ^ s)
      hinner_nonneg α
  have htrace :
      (CFC.rpow
          (CFC.rpow (Classical.diagonalState q hq_sum).m s *
            (Classical.diagonalState p hp_sum).m *
            CFC.rpow (Classical.diagonalState q hq_sum).m s) α).trace.re =
        ∑ i, ((q i : ℝ) ^ s * (p i : ℝ) * (q i : ℝ) ^ s) ^ α := by
    rw [hM, Matrix.trace_diagonal]
    simp
  have hsum :
      (∑ i, ((q i : ℝ) ^ s * (p i : ℝ) * (q i : ℝ) ^ s) ^ α) =
        ∑ i, ((p i : ℝ) ^ α) * ((q i : ℝ) ^ (1 - α)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simpa [s, mul_comm, mul_left_comm, mul_assoc] using
      diagonal_sandwiched_power_term (p i : ℝ) (q i : ℝ) α (hp_pos i) (hq_pos i) hα_pos
  unfold sandwichedRenyi
  change
    (1 / (α - 1)) *
        log2
          ((CFC.rpow
            (CFC.rpow (Classical.diagonalState q hq_sum).m s *
              (Classical.diagonalState p hp_sum).m *
              CFC.rpow (Classical.diagonalState q hq_sum).m s) α).trace.re) =
      (1 / (α - 1)) *
        log2 (∑ i, ((p i : ℝ) ^ α) * ((q i : ℝ) ^ (1 - α)))
  rw [htrace, hsum]

/-- On full-rank classical diagonal states, the sandwiched and Petz Renyi
divergences coincide. This is the commuting endpoint used by classical
reductions in the sandwiched-Renyi DPI proof route. -/
theorem sandwichedRenyi_diagonalState_eq_petzRenyi
    (p q : a → ℝ≥0) (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hp_pos : ∀ i, 0 < (p i : ℝ)) (hq_pos : ∀ i, 0 < (q i : ℝ))
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyi (Classical.diagonalState p hp_sum) (Classical.diagonalState q hq_sum)
        (Classical.diagonalState_posDef p hp_sum hp_pos)
        (Classical.diagonalState_posDef q hq_sum hq_pos)
        α hα_pos hα_ne_one =
      petzRenyi (Classical.diagonalState p hp_sum) (Classical.diagonalState q hq_sum)
        (Classical.diagonalState_posDef p hp_sum hp_pos)
        (Classical.diagonalState_posDef q hq_sum hq_pos)
        α hα_pos hα_ne_one := by
  rw [sandwichedRenyi_diagonalState_eq_classicalPowerSum p q hp_sum hq_sum
      hp_pos hq_pos α hα_pos hα_ne_one,
    petzRenyi_diagonalState_eq_classicalPowerSum p q hp_sum hq_sum
      hp_pos hq_pos α hα_pos hα_ne_one]

/-- Real powers of density matrices are positive semidefinite. -/
theorem rpowMatrix_posSemidef (ρ : MState a) (s : ℝ) :
    (CFC.rpow ρ.m s).PosSemidef :=
  renyi_cMatrix_rpow_posSemidef ρ.m s

/-- Real powers of positive-definite density matrices are positive definite. -/
theorem rpowMatrix_posDef_of_posDef (ρ : MState a) (hρ : ρ.m.PosDef) (s : ℝ) :
    (CFC.rpow ρ.m s).PosDef :=
  cMatrix_rpow_posDef_of_posDef hρ s

/-- The positive semidefinite inner operator
`σ^((1-α)/(2α)) ρ σ^((1-α)/(2α))` appearing in the sandwiched Renyi
divergence. -/
def sandwichedRenyiInner (ρ σ : MState a) (α : ℝ) : CMatrix a :=
  let s := (1 - α) / (2 * α)
  let C := CFC.rpow σ.m s
  C * ρ.m * C

/-- The positive-reference inner operator
`σ^((1-α)/(2α)) ρ σ^((1-α)/(2α))` for a non-normalized matrix reference. -/
def sandwichedRenyiReferenceInner (ρ : MState a) (σ : CMatrix a) (α : ℝ) :
    CMatrix a :=
  let s := (1 - α) / (2 * α)
  let C := CFC.rpow σ s
  C * ρ.m * C

/-- Matrix-level sandwiched Renyi `Q` functional
`Q_α(ρ, σ) = Tr[(σ^r ρ σ^r)^α]`, `r = (1 - α) / (2α)`.

Unlike `sandwichedRenyi`, this helper is intentionally stated at the matrix
level and only uses positive matrix powers in the low-`α` range
`1 / 2 < α < 1`.  The PSD witnesses document the intended domain; the
definition itself is proof-irrelevant and keeps the trace-power expression
available for singular Stinespring lifts. -/
def sandwichedRenyiQ
    (ρ σ : CMatrix a) (_hρ : ρ.PosSemidef) (_hσ : σ.PosSemidef)
    (α : ℝ) : ℝ :=
  let s := (1 - α) / (2 * α)
  let C := CFC.rpow σ s
  (CFC.rpow (C * ρ * C) α).trace.re

/-- The sandwiched Renyi inner operator is positive semidefinite. -/
theorem sandwichedRenyiInner_posSemidef (ρ σ : MState a) (α : ℝ) :
    (sandwichedRenyiInner ρ σ α).PosSemidef := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ.m s
  have hC : C.PosSemidef := by
    simpa [C] using σ.rpowMatrix_posSemidef s
  have hCstar : star C = C := hC.isHermitian.eq
  have hinner : (star C * ρ.m * C).PosSemidef :=
    Matrix.PosSemidef.conjTranspose_mul_mul_same ρ.psd C
  rw [hCstar] at hinner
  simpa [sandwichedRenyiInner, s, C] using hinner

/-- The matrix-reference sandwiched Renyi inner operator is positive
semidefinite whenever the reference matrix is PSD. -/
theorem sandwichedRenyiReferenceInner_posSemidef
    (ρ : MState a) {σ : CMatrix a} (_hσ : σ.PosSemidef) (α : ℝ) :
    (sandwichedRenyiReferenceInner ρ σ α).PosSemidef := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ s
  have hC : C.PosSemidef := by
    simpa [C] using renyi_cMatrix_rpow_posSemidef σ s
  have hCstar : star C = C := hC.isHermitian.eq
  have hinner : (star C * ρ.m * C).PosSemidef :=
    Matrix.PosSemidef.conjTranspose_mul_mul_same ρ.psd C
  rw [hCstar] at hinner
  simpa [sandwichedRenyiReferenceInner, s, C] using hinner

/-- The matrix-level `Q` functional specializes to the existing
`sandwichedRenyiInner` power trace on normalized states. -/
theorem sandwichedRenyiQ_eq_psdTracePower_inner
    (ρ σ : MState a) (α : ℝ) :
    sandwichedRenyiQ ρ.m σ.m ρ.psd σ.psd α =
      psdTracePower (sandwichedRenyiInner ρ σ α)
        (sandwichedRenyiInner_posSemidef ρ σ α) α := by
  unfold sandwichedRenyiQ sandwichedRenyiInner psdTracePower
  rfl

/-- The matrix-level `Q` functional is the power trace of the matrix-reference
sandwiched Renyi inner operator. -/
theorem sandwichedRenyiQ_eq_psdTracePower_referenceInner
    (ρ : MState a) {σ : CMatrix a} (hσ : σ.PosSemidef) (α : ℝ) :
    sandwichedRenyiQ ρ.m σ ρ.psd hσ α =
      psdTracePower (sandwichedRenyiReferenceInner ρ σ α)
        (sandwichedRenyiReferenceInner_posSemidef ρ hσ α) α := by
  unfold sandwichedRenyiQ sandwichedRenyiReferenceInner psdTracePower
  rfl

/-- The PSD-friendly low-`α` `Q` functional is invariant under simultaneous
unitary conjugation.

The explicit nonnegativity assumptions are exactly the low-`α` domain in
which this matrix-level helper is intended to be used: both the reference
sandwich exponent and the final trace-power exponent are nonnegative, so no
inverse of a singular reference is required. -/
theorem sandwichedRenyiQ_unitary_conj
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (U : Matrix.unitaryGroup a ℂ) (α : ℝ)
    (hs_nonneg : 0 ≤ (1 - α) / (2 * α)) (hα_nonneg : 0 ≤ α) :
    sandwichedRenyiQ
        ((U : CMatrix a) * ρ * star (U : CMatrix a))
        ((U : CMatrix a) * σ * star (U : CMatrix a))
        (by simpa using posSemidef_unitary_conj hρ U⁻¹)
        (by simpa using posSemidef_unitary_conj hσ U⁻¹) α =
      sandwichedRenyiQ ρ σ hρ hσ α := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ s
  let inner : CMatrix a := C * ρ * C
  have hσpow :
      CFC.rpow ((U : CMatrix a) * σ * star (U : CMatrix a)) s =
        (U : CMatrix a) * C * star (U : CMatrix a) := by
    simpa [C, Unitary.conjStarAlgAut_apply] using
      cMatrix_rpow_conjStarAlgAut_nonneg U hσ hs_nonneg
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
    Unitary.coe_star_mul_self U
  have hinner :
      CFC.rpow ((U : CMatrix a) * σ * star (U : CMatrix a)) s *
          ((U : CMatrix a) * ρ * star (U : CMatrix a)) *
          CFC.rpow ((U : CMatrix a) * σ * star (U : CMatrix a)) s =
        (U : CMatrix a) * inner * star (U : CMatrix a) := by
    rw [hσpow]
    calc
      ((U : CMatrix a) * C * star (U : CMatrix a)) *
          ((U : CMatrix a) * ρ * star (U : CMatrix a)) *
          ((U : CMatrix a) * C * star (U : CMatrix a)) =
          (U : CMatrix a) * C * (star (U : CMatrix a) * (U : CMatrix a)) *
            ρ * (star (U : CMatrix a) * (U : CMatrix a)) * C *
            star (U : CMatrix a) := by
            noncomm_ring
      _ = (U : CMatrix a) * C * 1 * ρ * 1 * C * star (U : CMatrix a) := by
            rw [hUstarU]
      _ = (U : CMatrix a) * inner * star (U : CMatrix a) := by
            simp [inner, Matrix.mul_assoc]
  have hC_hm : C.IsHermitian :=
    (renyi_cMatrix_rpow_posSemidef σ s).isHermitian
  have hinner_psd : inner.PosSemidef := by
    have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hρ C
    rwa [hC_hm.eq] at h
  have hpow :
      CFC.rpow
          (CFC.rpow ((U : CMatrix a) * σ * star (U : CMatrix a)) s *
            ((U : CMatrix a) * ρ * star (U : CMatrix a)) *
            CFC.rpow ((U : CMatrix a) * σ * star (U : CMatrix a)) s) α =
        (U : CMatrix a) * CFC.rpow inner α * star (U : CMatrix a) := by
    rw [hinner]
    simpa [Unitary.conjStarAlgAut_apply] using
      cMatrix_rpow_conjStarAlgAut_nonneg U hinner_psd hα_nonneg
  have htrace :
      (CFC.rpow
          (CFC.rpow ((U : CMatrix a) * σ * star (U : CMatrix a)) s *
            ((U : CMatrix a) * ρ * star (U : CMatrix a)) *
            CFC.rpow ((U : CMatrix a) * σ * star (U : CMatrix a)) s) α).trace.re =
        (CFC.rpow inner α).trace.re := by
    rw [hpow]
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
  unfold sandwichedRenyiQ
  change
    (CFC.rpow
      (CFC.rpow ((U : CMatrix a) * σ * star (U : CMatrix a)) s *
        ((U : CMatrix a) * ρ * star (U : CMatrix a)) *
        CFC.rpow ((U : CMatrix a) * σ * star (U : CMatrix a)) s) α).trace.re =
      (CFC.rpow inner α).trace.re
  rw [htrace]

/-- The PSD-friendly low-`α` `Q` functional is invariant under simultaneous
rectangular isometry conjugation.

This is the Stinespring handoff used by the strict low-`α` Gour/Frank--Lieb
route: for positive exponents, the reference power and the final trace power
commute with `X ↦ V X Vᴴ` because this map is a non-unital star homomorphism
and adds only zero eigenvalues. -/
theorem sandwichedRenyiQ_isometry_conj
    {r : Type v} [Fintype r] [DecidableEq r]
    (V : Matrix r a ℂ) (hV : Matrix.conjTranspose V * V = (1 : CMatrix a))
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (α : ℝ)
    (hs_pos : 0 < (1 - α) / (2 * α)) (hα_pos : 0 < α) :
    sandwichedRenyiQ
        (V * ρ * Matrix.conjTranspose V)
        (V * σ * Matrix.conjTranspose V)
        (hρ.mul_mul_conjTranspose_same V)
        (hσ.mul_mul_conjTranspose_same V) α =
      sandwichedRenyiQ ρ σ hρ hσ α := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ s
  have hσpow :
      CFC.rpow (V * σ * Matrix.conjTranspose V) s =
        V * C * Matrix.conjTranspose V := by
    simpa [C, s] using
      cMatrix_rpow_isometry_conj V hσ hV (s := s) hs_pos
  have hC : C.PosSemidef := by
    simpa [C] using cMatrix_rpow_posSemidef (A := σ) (s := s) hσ
  have hCstar : star C = C := hC.isHermitian.eq
  have hinnerPSD : (C * ρ * C).PosSemidef := by
    have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hρ C
    have hCct : Matrix.conjTranspose C = C := by
      simpa [Matrix.star_eq_conjTranspose] using hCstar
    rw [hCct] at h
    simpa [Matrix.mul_assoc] using h
  have hinner :
      CFC.rpow (V * σ * Matrix.conjTranspose V) s *
          (V * ρ * Matrix.conjTranspose V) *
          CFC.rpow (V * σ * Matrix.conjTranspose V) s =
        V * (C * ρ * C) * Matrix.conjTranspose V := by
    rw [hσpow]
    calc
      (V * C * Matrix.conjTranspose V) *
            (V * ρ * Matrix.conjTranspose V) *
            (V * C * Matrix.conjTranspose V) =
          V * C * (Matrix.conjTranspose V * V) * ρ *
            (Matrix.conjTranspose V * V) * C * Matrix.conjTranspose V := by
            simp [Matrix.mul_assoc]
      _ = V * C * (1 : CMatrix a) * ρ *
            (1 : CMatrix a) * C * Matrix.conjTranspose V := by
            rw [hV]
      _ = V * (C * ρ * C) * Matrix.conjTranspose V := by
            simp [Matrix.mul_assoc]
  unfold sandwichedRenyiQ
  dsimp only
  rw [hinner]
  exact psdTracePower_isometry_conj V hinnerPSD hV hα_pos

/-- The PSD-friendly low-`α` `Q` functional factorizes over tensor products
when the exponents are nonnegative.

This is the algebraic tensor step needed by a finite twirling proof of
partial-trace monotonicity: after twirling to `ρ_A ⊗ π_B` and `σ_A ⊗ π_B`,
the common normalized factor contributes multiplicatively. -/
theorem sandwichedRenyiQ_kronecker
    {b : Type v} [Fintype b] [DecidableEq b]
    {ρ₁ σ₁ : CMatrix a} {ρ₂ σ₂ : CMatrix b}
    (hρ₁ : ρ₁.PosSemidef) (hσ₁ : σ₁.PosSemidef)
    (hρ₂ : ρ₂.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    (α : ℝ) :
    sandwichedRenyiQ
        (Matrix.kronecker ρ₁ ρ₂)
        (Matrix.kronecker σ₁ σ₂)
        (hρ₁.kronecker hρ₂) (hσ₁.kronecker hσ₂) α =
      sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁ α *
        sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂ α := by
  let s : ℝ := (1 - α) / (2 * α)
  let C₁ : CMatrix a := CFC.rpow σ₁ s
  let C₂ : CMatrix b := CFC.rpow σ₂ s
  let inner₁ : CMatrix a := C₁ * ρ₁ * C₁
  let inner₂ : CMatrix b := C₂ * ρ₂ * C₂
  have hC :
      CFC.rpow (Matrix.kronecker σ₁ σ₂) s =
        Matrix.kronecker C₁ C₂ := by
    simpa [C₁, C₂, s] using cMatrix_rpow_kronecker hσ₁ hσ₂ s
  have hinner :
      CFC.rpow (Matrix.kronecker σ₁ σ₂) s *
          Matrix.kronecker ρ₁ ρ₂ *
          CFC.rpow (Matrix.kronecker σ₁ σ₂) s =
        Matrix.kronecker inner₁ inner₂ := by
    rw [hC]
    simp [inner₁, inner₂, Matrix.mul_kronecker_mul, Matrix.mul_assoc]
  have hC₁_hm : C₁.IsHermitian :=
    (renyi_cMatrix_rpow_posSemidef σ₁ s).isHermitian
  have hC₂_hm : C₂.IsHermitian :=
    (renyi_cMatrix_rpow_posSemidef σ₂ s).isHermitian
  have hinner₁_psd : inner₁.PosSemidef := by
    have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hρ₁ C₁
    rwa [hC₁_hm.eq] at h
  have hinner₂_psd : inner₂.PosSemidef := by
    have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hρ₂ C₂
    rwa [hC₂_hm.eq] at h
  have htraceC :
      (CFC.rpow
        (CFC.rpow (Matrix.kronecker σ₁ σ₂) s * Matrix.kronecker ρ₁ ρ₂ *
          CFC.rpow (Matrix.kronecker σ₁ σ₂) s) α).trace =
        (CFC.rpow inner₁ α).trace * (CFC.rpow inner₂ α).trace := by
    rw [hinner]
    rw [cMatrix_rpow_kronecker hinner₁_psd hinner₂_psd α]
    change
      (Matrix.kroneckerMap (fun x y => x * y)
        (CFC.rpow inner₁ α) (CFC.rpow inner₂ α)).trace =
        (CFC.rpow inner₁ α).trace * (CFC.rpow inner₂ α).trace
    rw [Matrix.trace_kronecker]
  have h_im1 : ((CFC.rpow inner₁ α).trace).im = 0 := by
    have htrace_nonneg : 0 ≤ (CFC.rpow inner₁ α).trace :=
      Matrix.PosSemidef.trace_nonneg
        (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := inner₁) (y := α)))
    exact htrace_nonneg.2.symm
  have h_im2 : ((CFC.rpow inner₂ α).trace).im = 0 := by
    have htrace_nonneg : 0 ≤ (CFC.rpow inner₂ α).trace :=
      Matrix.PosSemidef.trace_nonneg
        (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := inner₂) (y := α)))
    exact htrace_nonneg.2.symm
  unfold sandwichedRenyiQ
  change
    (CFC.rpow
      (CFC.rpow (Matrix.kronecker σ₁ σ₂) s * Matrix.kronecker ρ₁ ρ₂ *
        CFC.rpow (Matrix.kronecker σ₁ σ₂) s) α).trace.re =
      (CFC.rpow inner₁ α).trace.re * (CFC.rpow inner₂ α).trace.re
  rw [htraceC, Complex.mul_re, h_im1, h_im2]
  ring

/-- The sandwiched Renyi inner operator is positive definite in the full-rank
domain used by the current local `sandwichedRenyi` API. -/
theorem sandwichedRenyiInner_posDef
    (ρ σ : MState a) (hρ : ρ.m.PosDef) (hσ : σ.m.PosDef) (α : ℝ) :
    (sandwichedRenyiInner ρ σ α).PosDef := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ.m s
  have hC : C.PosDef := by
    simpa [C] using σ.rpowMatrix_posDef_of_posDef hσ s
  have hC_hm : C.IsHermitian := hC.posSemidef.isHermitian
  have hinner : (C * ρ.m * C).PosDef := by
    have h := hρ.mul_mul_conjTranspose_same (B := C) ?_
    · rwa [hC_hm.eq] at h
    · exact Matrix.vecMul_injective_of_isUnit hC.isUnit
  simpa [sandwichedRenyiInner, s, C] using hinner

/-- The matrix-reference sandwiched Renyi inner operator is positive definite
in the full-rank domain. -/
theorem sandwichedRenyiReferenceInner_posDef
    (ρ : MState a) {σ : CMatrix a} (hρ : ρ.m.PosDef) (hσ : σ.PosDef)
    (α : ℝ) :
    (sandwichedRenyiReferenceInner ρ σ α).PosDef := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ s
  have hC : C.PosDef := by
    simpa [C] using cMatrix_rpow_posDef_of_posDef hσ s
  have hC_hm : C.IsHermitian := hC.posSemidef.isHermitian
  have hinner : (C * ρ.m * C).PosDef := by
    have h := hρ.mul_mul_conjTranspose_same (B := C) ?_
    · rwa [hC_hm.eq] at h
    · exact Matrix.vecMul_injective_of_isUnit hC.isUnit
  simpa [sandwichedRenyiReferenceInner, s, C] using hinner

/-- With a positive-definite matrix reference, the matrix-reference sandwiched
Renyi inner operator is nonzero for every normalized state.

This removes an unnecessary full-rank assumption on the state side in
high-`α` support-domain arguments: the reference power is invertible, so
`σ^s ρ σ^s = 0` would force the state matrix itself to be zero. -/
theorem sandwichedRenyiReferenceInner_ne_zero_of_reference_posDef
    (ρ : MState a) {σ : CMatrix a} (hσ : σ.PosDef) (α : ℝ) :
    sandwichedRenyiReferenceInner ρ σ α ≠ 0 := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ s
  have hC : C.PosDef := by
    simpa [C] using cMatrix_rpow_posDef_of_posDef hσ s
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit
  have hleft : C⁻¹ * C = (1 : CMatrix a) := Matrix.nonsing_inv_mul C hCdet
  have hright : C * C⁻¹ = (1 : CMatrix a) := Matrix.mul_nonsing_inv C hCdet
  intro hzero
  have hzero' : C⁻¹ * (C * ρ.m * C) * C⁻¹ = 0 := by
    rw [show C * ρ.m * C = 0 by
      simpa [sandwichedRenyiReferenceInner, s, C] using hzero]
    simp
  have hρzero : ρ.m = 0 := by
    calc
      ρ.m = (1 : CMatrix a) * ρ.m * (1 : CMatrix a) := by simp
      _ = (C⁻¹ * C) * ρ.m * (C * C⁻¹) := by rw [hleft, hright]
      _ = C⁻¹ * (C * ρ.m * C) * C⁻¹ := by noncomm_ring
      _ = 0 := hzero'
  exact ρ.matrix_ne_zero hρzero

/-- The normalized-state sandwiched Renyi inner operator is nonzero whenever
the reference state is positive definite. -/
theorem sandwichedRenyiInner_ne_zero_of_reference_posDef
    (ρ σ : MState a) (hσ : σ.m.PosDef) (α : ℝ) :
    sandwichedRenyiInner ρ σ α ≠ 0 := by
  simpa [sandwichedRenyiInner, sandwichedRenyiReferenceInner] using
    sandwichedRenyiReferenceInner_ne_zero_of_reference_posDef
      ρ (σ := σ.m) hσ α

/-- A positive-definite matrix reference gives a strictly positive
matrix-reference sandwiched power trace, without requiring the state itself to
be full-rank. -/
theorem sandwichedRenyiReferenceInner_psdTracePower_pos_of_reference_posDef
    (ρ : MState a) {σ : CMatrix a} (hσ : σ.PosDef) (α : ℝ) :
    0 <
      psdTracePower (sandwichedRenyiReferenceInner ρ σ α)
        (sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef α) α :=
  psdTracePower_pos_of_ne_zero
    (sandwichedRenyiReferenceInner ρ σ α)
    (sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef α)
    (sandwichedRenyiReferenceInner_ne_zero_of_reference_posDef ρ hσ α)

/-- A positive-definite state reference gives a strictly positive sandwiched
power trace, without requiring the input state itself to be full-rank. -/
theorem sandwichedRenyiInner_psdTracePower_pos_of_reference_posDef
    (ρ σ : MState a) (hσ : σ.m.PosDef) (α : ℝ) :
    0 <
      psdTracePower (sandwichedRenyiInner ρ σ α)
        (sandwichedRenyiInner_posSemidef ρ σ α) α := by
  simpa [sandwichedRenyiInner, sandwichedRenyiReferenceInner] using
    sandwichedRenyiReferenceInner_psdTracePower_pos_of_reference_posDef
      ρ (σ := σ.m) hσ α

/-- The full-rank sandwiched Renyi inner operator has strictly positive PSD
power trace. This is the positivity side condition needed to turn core
trace-power inequalities into logarithmic Renyi inequalities. -/
theorem sandwichedRenyiInner_psdTracePower_pos
    (ρ σ : MState a) (hρ : ρ.m.PosDef) (hσ : σ.m.PosDef) (α : ℝ) :
    0 <
      psdTracePower (sandwichedRenyiInner ρ σ α)
        (sandwichedRenyiInner_posSemidef ρ σ α) α := by
  classical
  have : Nonempty a := ρ.nonempty
  rw [psdTracePower_eq_sum_eigenvalues_rpow]
  exact Finset.sum_pos' (fun i _ =>
      le_of_lt (Real.rpow_pos_of_pos
        ((sandwichedRenyiInner_posDef ρ σ hρ hσ α).eigenvalues_pos i) α)
    )
    ⟨Classical.choice ρ.nonempty, Finset.mem_univ _,
      Real.rpow_pos_of_pos
        ((sandwichedRenyiInner_posDef ρ σ hρ hσ α).eigenvalues_pos
          (Classical.choice ρ.nonempty)) α⟩

/-- The full-rank matrix-reference inner operator has strictly positive PSD
power trace. -/
theorem sandwichedRenyiReferenceInner_psdTracePower_pos
    (ρ : MState a) {σ : CMatrix a} (hρ : ρ.m.PosDef) (hσ : σ.PosDef)
    (α : ℝ) :
    0 <
      psdTracePower (sandwichedRenyiReferenceInner ρ σ α)
        (sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef α) α := by
  classical
  have : Nonempty a := ρ.nonempty
  rw [psdTracePower_eq_sum_eigenvalues_rpow]
  exact Finset.sum_pos' (fun i _ =>
      le_of_lt (Real.rpow_pos_of_pos
        ((sandwichedRenyiReferenceInner_posDef ρ hρ hσ α).eigenvalues_pos i) α)
    )
    ⟨Classical.choice ρ.nonempty, Finset.mem_univ _,
      Real.rpow_pos_of_pos
        ((sandwichedRenyiReferenceInner_posDef ρ hρ hσ α).eigenvalues_pos
          (Classical.choice ρ.nonempty)) α⟩

/-- Scaling the matrix reference scales the sandwiched inner operator by the
two reference-side power factors. -/
theorem sandwichedRenyiReferenceInner_real_smul_reference
    (ρ : MState a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (α : ℝ) :
    let s : ℝ := (1 - α) / (2 * α)
    sandwichedRenyiReferenceInner ρ (lambda • σ : CMatrix a) α =
      ((lambda ^ s * lambda ^ s : ℝ) •
        sandwichedRenyiReferenceInner ρ σ α : CMatrix a) := by
  intro s
  unfold sandwichedRenyiReferenceInner
  change
    CFC.rpow (lambda • σ : CMatrix a) s * ρ.m *
        CFC.rpow (lambda • σ : CMatrix a) s =
      ((lambda ^ s * lambda ^ s : ℝ) •
        (CFC.rpow σ s * ρ.m * CFC.rpow σ s) : CMatrix a)
  rw [cMatrix_rpow_real_smul_posSemidef_schatten hσ hlambda]
  simp [smul_smul, mul_assoc]

/-- Trace-power form of reference scaling for the matrix-reference sandwiched
inner operator. -/
theorem sandwichedRenyiReferenceInner_psdTracePower_real_smul_reference
    (ρ : MState a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (α : ℝ) :
    let s : ℝ := (1 - α) / (2 * α)
    psdTracePower
        (sandwichedRenyiReferenceInner ρ (lambda • σ : CMatrix a) α)
        (sandwichedRenyiReferenceInner_posSemidef ρ
          (Matrix.PosSemidef.smul hσ hlambda) α)
        α =
      ((lambda ^ s * lambda ^ s) ^ α) *
        psdTracePower
          (sandwichedRenyiReferenceInner ρ σ α)
          (sandwichedRenyiReferenceInner_posSemidef ρ hσ α)
          α := by
  intro s
  have hfactor_nonneg : 0 ≤ lambda ^ s * lambda ^ s :=
    mul_nonneg (Real.rpow_nonneg hlambda s) (Real.rpow_nonneg hlambda s)
  unfold psdTracePower
  rw [sandwichedRenyiReferenceInner_real_smul_reference ρ hσ hlambda α]
  rw [cMatrix_rpow_real_smul_posSemidef_schatten
    (sandwichedRenyiReferenceInner_posSemidef ρ hσ α) hfactor_nonneg]
  rw [Matrix.trace_smul]
  simp

/-- The scalar factor created by scaling the reference side of the sandwiched
Renyi inner operator. -/
private theorem sandwichedRenyiReference_scale_factor
    {lambda α : ℝ} (hlambda : 0 < lambda) (hα_pos : 0 < α) :
    let s : ℝ := (1 - α) / (2 * α)
    (lambda ^ s * lambda ^ s) ^ α = lambda ^ (1 - α) := by
  intro s
  have hlambda_nonneg : 0 ≤ lambda := le_of_lt hlambda
  have hmul : lambda ^ s * lambda ^ s = lambda ^ (s + s) := by
    rw [Real.rpow_add hlambda]
  calc
    (lambda ^ s * lambda ^ s) ^ α = (lambda ^ (s + s)) ^ α := by
      rw [hmul]
    _ = lambda ^ ((s + s) * α) := by
      rw [← Real.rpow_mul hlambda_nonneg]
    _ = lambda ^ (1 - α) := by
      congr 1
      dsimp [s]
      field_simp [ne_of_gt hα_pos]
      ring_nf

/-- Scaling a PSD reference by a positive real multiplies the sandwiched
`Q_alpha` functional by `scale^(1-alpha)`.

This is the scalar-reference identity used in Tomamichel's uncertainty proof
before taking logarithms. -/
theorem sandwichedRenyiQ_real_smul_reference_of_pos
    (rho : MState a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    {scale : ℝ} (hScale : 0 < scale) (alpha : ℝ) (hAlpha : 0 < alpha) :
    sandwichedRenyiQ rho.m (scale • sigma) rho.psd
        (Matrix.PosSemidef.smul hSigma hScale.le) alpha =
      scale ^ (1 - alpha) *
        sandwichedRenyiQ rho.m sigma rho.psd hSigma alpha := by
  have hPower :=
    sandwichedRenyiReferenceInner_psdTracePower_real_smul_reference
      rho hSigma hScale.le alpha
  have hFactor :
      (scale ^ ((1 - alpha) / (2 * alpha)) *
          scale ^ ((1 - alpha) / (2 * alpha))) ^ alpha =
        scale ^ (1 - alpha) := by
    have hMul :
        scale ^ ((1 - alpha) / (2 * alpha)) *
            scale ^ ((1 - alpha) / (2 * alpha)) =
          scale ^ (((1 - alpha) / (2 * alpha)) +
            ((1 - alpha) / (2 * alpha))) := by
      rw [Real.rpow_add hScale]
    rw [hMul, ← Real.rpow_mul hScale.le]
    congr 1
    field_simp [ne_of_gt hAlpha]
    ring
  rw [sandwichedRenyiQ_eq_psdTracePower_referenceInner,
    sandwichedRenyiQ_eq_psdTracePower_referenceInner]
  rw [hPower, hFactor]

/-- Definition bridge from sandwiched Renyi divergence to the PSD power trace
used by the Schatten variational API. -/
theorem sandwichedRenyi_eq_log2_psdTracePower_inner
    (ρ σ : MState a) (hρ : ρ.m.PosDef) (hσ : σ.m.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyi ρ σ hρ hσ α hα_pos hα_ne_one =
      (1 / (α - 1)) *
        log2 (psdTracePower (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α) := by
  unfold sandwichedRenyi sandwichedRenyiInner psdTracePower
  rfl

/-- Definition bridge from the matrix-reference sandwiched Renyi divergence to
the PSD power trace used by the Schatten variational API. -/
theorem sandwichedRenyiReference_eq_log2_psdTracePower_inner
    (ρ : MState a) {σ : CMatrix a} (hρ : ρ.m.PosDef) (hσ : σ.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyiReference ρ σ hρ hσ α hα_pos hα_ne_one =
      (1 / (α - 1)) *
        log2 (psdTracePower (sandwichedRenyiReferenceInner ρ σ α)
          (sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef α) α) := by
  unfold sandwichedRenyiReference sandwichedRenyiReferenceInner psdTracePower
  rfl

/-- Scaling a positive-definite matrix reference shifts the sandwiched Renyi
divergence by the logarithm of the scaling factor. -/
theorem sandwichedRenyiReference_real_smul_reference
    (ρ : MState a) {σ : CMatrix a} (hρ : ρ.m.PosDef) (hσ : σ.PosDef)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyiReference ρ (lambda • σ : CMatrix a) hρ
        (Matrix.PosDef.smul hσ hlambda) α hα_pos hα_ne_one =
      sandwichedRenyiReference ρ σ hρ hσ α hα_pos hα_ne_one - log2 lambda := by
  let s : ℝ := (1 - α) / (2 * α)
  have hlambda_nonneg : 0 ≤ lambda := le_of_lt hlambda
  have htrace_scale :
      psdTracePower
          (sandwichedRenyiReferenceInner ρ (lambda • σ : CMatrix a) α)
          (sandwichedRenyiReferenceInner_posSemidef ρ
            (Matrix.PosDef.smul hσ hlambda).posSemidef α)
          α =
        ((lambda ^ s * lambda ^ s) ^ α) *
          psdTracePower
            (sandwichedRenyiReferenceInner ρ σ α)
            (sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef α)
            α := by
    simpa [s] using
      sandwichedRenyiReferenceInner_psdTracePower_real_smul_reference
        ρ hσ.posSemidef hlambda_nonneg α
  have hfactor :
      (lambda ^ s * lambda ^ s) ^ α = lambda ^ (1 - α) := by
    simpa [s] using sandwichedRenyiReference_scale_factor
      (lambda := lambda) (α := α) hlambda hα_pos
  have hfactor_pos : 0 < lambda ^ (1 - α) :=
    Real.rpow_pos_of_pos hlambda _
  have hTpos :
      0 <
        psdTracePower
          (sandwichedRenyiReferenceInner ρ σ α)
          (sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef α)
          α :=
    sandwichedRenyiReferenceInner_psdTracePower_pos ρ hρ hσ α
  have hlog_factor : log2 (lambda ^ (1 - α)) = (1 - α) * log2 lambda := by
    unfold log2
    rw [Real.log_rpow hlambda]
    ring
  have hcoef :
      (1 / (α - 1)) * ((1 - α) * log2 lambda) = -log2 lambda := by
    field_simp [hα_ne_one]
    ring
  rw [sandwichedRenyiReference_eq_log2_psdTracePower_inner]
  rw [sandwichedRenyiReference_eq_log2_psdTracePower_inner]
  rw [htrace_scale, hfactor]
  rw [log2_mul (ne_of_gt hfactor_pos) (ne_of_gt hTpos), hlog_factor]
  rw [mul_add, hcoef]
  ring

private theorem petzRenyi_trace_re_pos (ρ σ : MState a)
    (hρ : ρ.m.PosDef) (hσ : σ.m.PosDef) (α : ℝ) :
    0 < ((CFC.rpow ρ.m α * CFC.rpow σ.m (1 - α)).trace).re := by
  have : Nonempty a := ρ.nonempty
  exact trace_mul_posDef_re_pos
    (ρ.rpowMatrix_posDef_of_posDef hρ α)
    (σ.rpowMatrix_posDef_of_posDef hσ (1 - α))

theorem petzRenyi_prod {b : Type v} [Fintype b] [DecidableEq b]
    (ρ₁ σ₁ : MState a) (ρ₂ σ₂ : MState b)
    (hρ₁ : ρ₁.m.PosDef) (hσ₁ : σ₁.m.PosDef)
    (hρ₂ : ρ₂.m.PosDef) (hσ₂ : σ₂.m.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    (ρ₁.prod ρ₂).petzRenyi (σ₁.prod σ₂)
        (MState.PosDef.kron hρ₁ hρ₂) (MState.PosDef.kron hσ₁ hσ₂)
        α hα_pos hα_ne_one =
      ρ₁.petzRenyi σ₁ hρ₁ hσ₁ α hα_pos hα_ne_one +
        ρ₂.petzRenyi σ₂ hρ₂ hσ₂ α hα_pos hα_ne_one := by
  unfold petzRenyi
  have htrace :
      ((CFC.rpow (ρ₁.prod ρ₂).m α *
          CFC.rpow (σ₁.prod σ₂).m (1 - α)).trace).re =
        ((CFC.rpow ρ₁.m α * CFC.rpow σ₁.m (1 - α)).trace).re *
          ((CFC.rpow ρ₂.m α * CFC.rpow σ₂.m (1 - α)).trace).re := by
    have htraceC :
        (CFC.rpow (ρ₁.prod ρ₂).m α *
            CFC.rpow (σ₁.prod σ₂).m (1 - α)).trace =
          (CFC.rpow ρ₁.m α * CFC.rpow σ₁.m (1 - α)).trace *
            (CFC.rpow ρ₂.m α * CFC.rpow σ₂.m (1 - α)).trace := by
      rw [prod_m ρ₁ ρ₂, prod_m σ₁ σ₂, ← Matrix.kronecker]
      rw [cMatrix_rpow_kronecker hρ₁.posSemidef hρ₂.posSemidef α]
      rw [cMatrix_rpow_kronecker hσ₁.posSemidef hσ₂.posSemidef (1 - α)]
      change
        (Matrix.kroneckerMap (fun x y => x * y)
          (CFC.rpow ρ₁.m α) (CFC.rpow ρ₂.m α) *
        Matrix.kroneckerMap (fun x y => x * y)
          (CFC.rpow σ₁.m (1 - α)) (CFC.rpow σ₂.m (1 - α))).trace =
        (CFC.rpow ρ₁.m α * CFC.rpow σ₁.m (1 - α)).trace *
          (CFC.rpow ρ₂.m α * CFC.rpow σ₂.m (1 - α)).trace
      rw [← Matrix.mul_kronecker_mul]
      rw [Matrix.trace_kronecker]
    have h_im1 :
        ((CFC.rpow ρ₁.m α * CFC.rpow σ₁.m (1 - α)).trace).im = 0 :=
      trace_mul_posSemidef_im_eq_zero (ρ₁.rpowMatrix_posSemidef α)
        (σ₁.rpowMatrix_posSemidef (1 - α))
    have h_im2 :
        ((CFC.rpow ρ₂.m α * CFC.rpow σ₂.m (1 - α)).trace).im = 0 :=
      trace_mul_posSemidef_im_eq_zero (ρ₂.rpowMatrix_posSemidef α)
        (σ₂.rpowMatrix_posSemidef (1 - α))
    rw [htraceC, Complex.mul_re, h_im1, h_im2]
    ring
  have hxpos : 0 < ((CFC.rpow ρ₁.m α *
      CFC.rpow σ₁.m (1 - α)).trace).re :=
    petzRenyi_trace_re_pos ρ₁ σ₁ hρ₁ hσ₁ α
  have hypos : 0 < ((CFC.rpow ρ₂.m α *
      CFC.rpow σ₂.m (1 - α)).trace).re :=
    petzRenyi_trace_re_pos ρ₂ σ₂ hρ₂ hσ₂ α
  change (1 / (α - 1)) *
      log2 ((CFC.rpow (ρ₁.prod ρ₂).m α *
          CFC.rpow (σ₁.prod σ₂).m (1 - α)).trace).re =
    (1 / (α - 1)) *
      log2 ((CFC.rpow ρ₁.m α *
          CFC.rpow σ₁.m (1 - α)).trace).re +
    (1 / (α - 1)) *
      log2 ((CFC.rpow ρ₂.m α *
          CFC.rpow σ₂.m (1 - α)).trace).re
  rw [htrace]
  rw [log2_mul (ne_of_gt hxpos) (ne_of_gt hypos)]
  ring

theorem petzRenyi_tensorPower (ρ σ : MState a)
    (hρ : ρ.m.PosDef) (hσ : σ.m.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : ℕ) :
    (ρ.tensorPower n).petzRenyi (σ.tensorPower n)
        (ρ.tensorPower_posDef hρ n) (σ.tensorPower_posDef hσ n)
        α hα_pos hα_ne_one =
      (n : ℝ) * ρ.petzRenyi σ hρ hσ α hα_pos hα_ne_one := by
  induction n with
  | zero =>
      unfold petzRenyi
      simp only [MState.tensorPower_zero_matrix]
      rw [Nat.cast_zero, zero_mul]
      change 1 / (α - 1) *
          log2 (((1 : CMatrix PUnit) ^ α * (1 : CMatrix PUnit) ^ (1 - α)).trace).re =
        0
      rw [show ((1 : CMatrix PUnit) ^ α) = 1 by exact CFC.one_rpow,
        show ((1 : CMatrix PUnit) ^ (1 - α)) = 1 by exact CFC.one_rpow,
        one_mul, Matrix.trace_one]
      simp [log2]
  | succ n ih =>
      change (ρ.prod (ρ.tensorPower n)).petzRenyi (σ.prod (σ.tensorPower n))
          _ _ α hα_pos hα_ne_one =
        ↑(n + 1) * ρ.petzRenyi σ hρ hσ α hα_pos hα_ne_one
      rw [MState.petzRenyi_prod ρ σ (ρ.tensorPower n) (σ.tensorPower n)
        hρ hσ (ρ.tensorPower_posDef hρ n) (σ.tensorPower_posDef hσ n)
        α hα_pos hα_ne_one]
      rw [ih]
      rw [Nat.cast_add, Nat.cast_one]
      ring_nf

theorem sandwichedRenyi_prod {b : Type v} [Fintype b] [DecidableEq b]
    (ρ₁ σ₁ : MState a) (ρ₂ σ₂ : MState b)
    (hρ₁ : ρ₁.m.PosDef) (hσ₁ : σ₁.m.PosDef)
    (hρ₂ : ρ₂.m.PosDef) (hσ₂ : σ₂.m.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    (ρ₁.prod ρ₂).sandwichedRenyi (σ₁.prod σ₂)
        (MState.PosDef.kron hρ₁ hρ₂) (MState.PosDef.kron hσ₁ hσ₂)
        α hα_pos hα_ne_one =
      ρ₁.sandwichedRenyi σ₁ hρ₁ hσ₁ α hα_pos hα_ne_one +
        ρ₂.sandwichedRenyi σ₂ hρ₂ hσ₂ α hα_pos hα_ne_one := by
  unfold sandwichedRenyi
  let s := (1 - α) / (2 * α)
  have hC :
      CFC.rpow (σ₁.prod σ₂).m s =
        Matrix.kronecker (CFC.rpow σ₁.m s) (CFC.rpow σ₂.m s) := by
    rw [prod_m σ₁ σ₂]
    exact cMatrix_rpow_kronecker hσ₁.posSemidef hσ₂.posSemidef s
  have hinner :
      CFC.rpow (σ₁.prod σ₂).m s * (ρ₁.prod ρ₂).m *
          CFC.rpow (σ₁.prod σ₂).m s =
        Matrix.kronecker
          (CFC.rpow σ₁.m s * ρ₁.m * CFC.rpow σ₁.m s)
          (CFC.rpow σ₂.m s * ρ₂.m * CFC.rpow σ₂.m s) := by
    rw [hC, prod_m ρ₁ ρ₂]
    simp [Matrix.mul_kronecker_mul, Matrix.mul_assoc]
  have hinner₁_pos :
      (CFC.rpow σ₁.m s * ρ₁.m * CFC.rpow σ₁.m s).PosDef := by
    have hC₁ : (CFC.rpow σ₁.m s).PosDef :=
      σ₁.rpowMatrix_posDef_of_posDef hσ₁ s
    have hC₁_hm : (CFC.rpow σ₁.m s).IsHermitian :=
      (renyi_cMatrix_rpow_posSemidef σ₁.m s).isHermitian
    have h := hρ₁.mul_mul_conjTranspose_same (B := CFC.rpow σ₁.m s) ?_
    · rwa [hC₁_hm.eq] at h
    · exact Matrix.vecMul_injective_of_isUnit hC₁.isUnit
  have hinner₂_pos :
      (CFC.rpow σ₂.m s * ρ₂.m * CFC.rpow σ₂.m s).PosDef := by
    have hC₂ : (CFC.rpow σ₂.m s).PosDef :=
      σ₂.rpowMatrix_posDef_of_posDef hσ₂ s
    have hC₂_hm : (CFC.rpow σ₂.m s).IsHermitian :=
      (renyi_cMatrix_rpow_posSemidef σ₂.m s).isHermitian
    have h := hρ₂.mul_mul_conjTranspose_same (B := CFC.rpow σ₂.m s) ?_
    · rwa [hC₂_hm.eq] at h
    · exact Matrix.vecMul_injective_of_isUnit hC₂.isUnit
  have htrace :
      ((CFC.rpow
        (CFC.rpow (σ₁.prod σ₂).m s * (ρ₁.prod ρ₂).m *
          CFC.rpow (σ₁.prod σ₂).m s) α).trace).re =
        ((CFC.rpow
          (CFC.rpow σ₁.m s * ρ₁.m * CFC.rpow σ₁.m s) α).trace).re *
          ((CFC.rpow
            (CFC.rpow σ₂.m s * ρ₂.m * CFC.rpow σ₂.m s) α).trace).re := by
    have htraceC :
        (CFC.rpow
          (CFC.rpow (σ₁.prod σ₂).m s * (ρ₁.prod ρ₂).m *
            CFC.rpow (σ₁.prod σ₂).m s) α).trace =
          (CFC.rpow
            (CFC.rpow σ₁.m s * ρ₁.m * CFC.rpow σ₁.m s) α).trace *
            (CFC.rpow
              (CFC.rpow σ₂.m s * ρ₂.m * CFC.rpow σ₂.m s) α).trace := by
      rw [hinner]
      rw [cMatrix_rpow_kronecker hinner₁_pos.posSemidef hinner₂_pos.posSemidef α]
      change
        (Matrix.kroneckerMap (fun x y => x * y)
          (CFC.rpow
            (CFC.rpow σ₁.m s * ρ₁.m * CFC.rpow σ₁.m s) α)
          (CFC.rpow
            (CFC.rpow σ₂.m s * ρ₂.m * CFC.rpow σ₂.m s) α)).trace =
          (CFC.rpow
            (CFC.rpow σ₁.m s * ρ₁.m * CFC.rpow σ₁.m s) α).trace *
            (CFC.rpow
              (CFC.rpow σ₂.m s * ρ₂.m * CFC.rpow σ₂.m s) α).trace
      rw [Matrix.trace_kronecker]
    have h_im1 :
        ((CFC.rpow
          (CFC.rpow σ₁.m s * ρ₁.m * CFC.rpow σ₁.m s) α).trace).im = 0 := by
      have hpsd := hinner₁_pos.posSemidef
      have htrace_nonneg : 0 ≤
          (CFC.rpow (CFC.rpow σ₁.m s * ρ₁.m *
            CFC.rpow σ₁.m s) α).trace :=
        Matrix.PosSemidef.trace_nonneg
          (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg
            (a := CFC.rpow σ₁.m s * ρ₁.m * CFC.rpow σ₁.m s)
            (y := α)))
      exact htrace_nonneg.2.symm
    have h_im2 :
        ((CFC.rpow
          (CFC.rpow σ₂.m s * ρ₂.m * CFC.rpow σ₂.m s) α).trace).im = 0 := by
      have htrace_nonneg : 0 ≤
          (CFC.rpow (CFC.rpow σ₂.m s * ρ₂.m *
            CFC.rpow σ₂.m s) α).trace :=
        Matrix.PosSemidef.trace_nonneg
          (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg
            (a := CFC.rpow σ₂.m s * ρ₂.m * CFC.rpow σ₂.m s)
            (y := α)))
      exact htrace_nonneg.2.symm
    rw [htraceC, Complex.mul_re, h_im1, h_im2]
    ring
  have hxpos : 0 < ((CFC.rpow
      (CFC.rpow σ₁.m s * ρ₁.m * CFC.rpow σ₁.m s) α).trace).re := by
    have : Nonempty a := ρ₁.nonempty
    exact (Complex.pos_iff.mp (Matrix.PosDef.trace_pos
      (cMatrix_rpow_posDef_of_posDef hinner₁_pos α))).1
  have hypos : 0 < ((CFC.rpow
      (CFC.rpow σ₂.m s * ρ₂.m * CFC.rpow σ₂.m s) α).trace).re := by
    have : Nonempty b := ρ₂.nonempty
    exact (Complex.pos_iff.mp (Matrix.PosDef.trace_pos
      (cMatrix_rpow_posDef_of_posDef hinner₂_pos α))).1
  change (1 / (α - 1)) *
      log2 ((CFC.rpow
        (CFC.rpow (σ₁.prod σ₂).m s * (ρ₁.prod ρ₂).m *
          CFC.rpow (σ₁.prod σ₂).m s) α).trace).re =
    (1 / (α - 1)) *
      log2 ((CFC.rpow
        (CFC.rpow σ₁.m s * ρ₁.m * CFC.rpow σ₁.m s) α).trace).re +
    (1 / (α - 1)) *
      log2 ((CFC.rpow
        (CFC.rpow σ₂.m s * ρ₂.m * CFC.rpow σ₂.m s) α).trace).re
  rw [htrace]
  rw [log2_mul (ne_of_gt hxpos) (ne_of_gt hypos)]
  ring

theorem sandwichedRenyi_tensorPower (ρ σ : MState a)
    (hρ : ρ.m.PosDef) (hσ : σ.m.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : ℕ) :
    (ρ.tensorPower n).sandwichedRenyi (σ.tensorPower n)
        (ρ.tensorPower_posDef hρ n) (σ.tensorPower_posDef hσ n)
        α hα_pos hα_ne_one =
      (n : ℝ) * ρ.sandwichedRenyi σ hρ hσ α hα_pos hα_ne_one := by
  induction n with
  | zero =>
      unfold sandwichedRenyi
      simp only [MState.tensorPower_zero_matrix]
      rw [Nat.cast_zero, zero_mul]
      change 1 / (α - 1) *
          log2 ((((1 : CMatrix PUnit) ^ ((1 - α) / (2 * α)) *
              1 * (1 : CMatrix PUnit) ^ ((1 - α) / (2 * α))) ^ α).trace).re =
        0
      rw [show ((1 : CMatrix PUnit) ^ ((1 - α) / (2 * α))) = 1 by exact CFC.one_rpow,
        one_mul, mul_one,
        show ((1 : CMatrix PUnit) ^ α) = 1 by exact CFC.one_rpow,
        Matrix.trace_one]
      simp [log2]
  | succ n ih =>
      change (ρ.prod (ρ.tensorPower n)).sandwichedRenyi (σ.prod (σ.tensorPower n))
          _ _ α hα_pos hα_ne_one =
        ↑(n + 1) * ρ.sandwichedRenyi σ hρ hσ α hα_pos hα_ne_one
      rw [MState.sandwichedRenyi_prod ρ σ (ρ.tensorPower n) (σ.tensorPower n)
        hρ hσ (ρ.tensorPower_posDef hρ n) (σ.tensorPower_posDef hσ n)
        α hα_pos hα_ne_one]
      rw [ih]
      rw [Nat.cast_add, Nat.cast_one]
      ring_nf

/-- Tensor-power additivity of the Petz and sandwiched Renyi divergences. -/
theorem renyi_tensorPower_additivity (ρ σ : MState a)
    (hρ : ρ.m.PosDef) (hσ : σ.m.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : ℕ) :
    (ρ.tensorPower n).petzRenyi (σ.tensorPower n)
        (ρ.tensorPower_posDef hρ n) (σ.tensorPower_posDef hσ n)
        α hα_pos hα_ne_one =
          (n : ℝ) * ρ.petzRenyi σ hρ hσ α hα_pos hα_ne_one ∧
    (ρ.tensorPower n).sandwichedRenyi (σ.tensorPower n)
        (ρ.tensorPower_posDef hρ n) (σ.tensorPower_posDef hσ n)
        α hα_pos hα_ne_one =
          (n : ℝ) * ρ.sandwichedRenyi σ hρ hσ α hα_pos hα_ne_one := by
  exact ⟨MState.petzRenyi_tensorPower ρ σ hρ hσ α hα_pos hα_ne_one n,
    MState.sandwichedRenyi_tensorPower ρ σ hρ hσ α hα_pos hα_ne_one n⟩

end MState
