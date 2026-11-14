/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.Matrix
public import QIT.Util.SDP.HermitianPSDTraceDuality
public import QIT.States.TraceNorm.PositivePartBlock
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Audenaert fractional-power resolvent API

This module packages the mathlib CFC existential-measure representation for
finite complex matrices and adds the resolvent bridge used in Audenaert's
Appendix A argument.  The measure theorem is intentionally restricted to
`p ∈ (0, 1)`; the endpoint facts for `0` and `1` are exposed separately.

The source proof uses this fractional-power/resolvent reduction before the
block-decomposition positivity argument
[Audenaert2006QuantumChernoff, audenaert-2006-quantum-chernoff.tex:478-550].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Topology Matrix.Norms.L2Operator
open Matrix MeasureTheory Set intervalIntegral

namespace QIT

universe u v

noncomputable section

noncomputable local instance cMatrixCStarAlgebra
    {a : Type u} [Fintype a] [DecidableEq a] : CStarAlgebra (CMatrix a) := {}

noncomputable instance cMatrixContinuousENorm
    {a : Type u} [Fintype a] [DecidableEq a] : ContinuousENorm (CMatrix a) :=
  SeminormedAddGroup.toContinuousENorm

noncomputable instance cMatrixENormedAddMonoid
    {a : Type u} [Fintype a] [DecidableEq a] : ENormedAddMonoid (CMatrix a) :=
  NormedAddGroup.toENormedAddMonoid

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- CFC integrand used by mathlib's existential fractional-power representation. -/
def audenaertRpowIntegrand (p r : ℝ) (A : CMatrix a) : CMatrix a :=
  cfcₙ (Real.rpowIntegrand₀₁ p r) A

/-- The finite-dimensional resolvent form of the CFC integrand. -/
def audenaertResolventIntegrand (p r : ℝ) (A : CMatrix a) : CMatrix a :=
  r ^ (p - 1) • (A * (A + r • (1 : CMatrix a))⁻¹)

omit [Fintype a] in
private theorem cMatrix_real_smul_one_posDef {r : ℝ} (hr : 0 < r) :
    (r • (1 : CMatrix a)).PosDef := by
  rw [show r • (1 : CMatrix a) = Matrix.diagonal (fun _ : a => (r : ℂ)) by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]]
  rw [Matrix.posDef_diagonal_iff]
  intro i
  exact_mod_cast hr

omit [Fintype a] in
/-- For PSD `A` and `0 < r`, `A + r • 1` is positive definite. -/
theorem audenaertResolvent_posDef {r : ℝ} {A : CMatrix a}
    (hr : 0 < r) (hA : A.PosSemidef) :
    (A + r • (1 : CMatrix a)).PosDef :=
  Matrix.PosDef.posSemidef_add hA (cMatrix_real_smul_one_posDef hr)

/-- For PSD `A` and `0 < r`, `A + r • 1` is invertible. -/
theorem audenaertResolvent_isUnit {r : ℝ} {A : CMatrix a}
    (hr : 0 < r) (hA : A.PosSemidef) :
    IsUnit (A + r • (1 : CMatrix a)) :=
  (audenaertResolvent_posDef hr hA).isUnit

/-- The affine path from `B` to `A`, written with `Δ = A - B`. -/
def audenaertPathMatrix (A B : CMatrix a) (u : ℝ) : CMatrix a :=
  B + u • (A - B)

/-- The resolvent along Audenaert's affine path. -/
def audenaertPathResolvent (A B : CMatrix a) (u r : ℝ) : CMatrix a :=
  (audenaertPathMatrix A B u + r • (1 : CMatrix a))⁻¹

omit [Fintype a] [DecidableEq a] in
/-- The affine path is a convex combination of its PSD endpoints. -/
public theorem audenaertPathMatrix_posSemidef {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (audenaertPathMatrix A B u).PosSemidef := by
  have hconv :
      audenaertPathMatrix A B u = u • A + (1 - u) • B := by
    ext i j
    simp [audenaertPathMatrix, sub_eq_add_neg, smul_add, add_comm]
    ring
  rw [hconv]
  exact Matrix.PosSemidef.add
    (Matrix.PosSemidef.smul hA hu0)
    (Matrix.PosSemidef.smul hB (sub_nonneg.mpr hu1))

omit [Fintype a] in
/-- Along the PSD path, adding `r • 1` is positive definite for `0 < r`. -/
public theorem audenaertPathResolvent_posDef {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    {u r : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hr : 0 < r) :
    (audenaertPathMatrix A B u + r • (1 : CMatrix a)).PosDef :=
  audenaertResolvent_posDef hr (audenaertPathMatrix_posSemidef hA hB hu0 hu1)

/-- Along the PSD path, the shifted resolvent is invertible for `0 < r`. -/
public theorem audenaertPathResolvent_isUnit {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    {u r : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hr : 0 < r) :
    IsUnit (audenaertPathMatrix A B u + r • (1 : CMatrix a)) :=
  (audenaertPathResolvent_posDef hA hB hu0 hu1 hr).isUnit

/-- The path resolvent is Hermitian. -/
public theorem audenaertPathResolvent_isHermitian {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    {u r : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hr : 0 < r) :
    (audenaertPathResolvent A B u r).IsHermitian := by
  exact (audenaertPathResolvent_posDef hA hB hu0 hu1 hr).isHermitian.inv

/-- The path resolvent is positive semidefinite. -/
public theorem audenaertPathResolvent_posSemidef {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    {u r : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hr : 0 < r) :
    (audenaertPathResolvent A B u r).PosSemidef := by
  exact (audenaertPathResolvent_posDef hA hB hu0 hu1 hr).posSemidef.inv

private theorem spectralSignBlockMatrix_posSemidef
    (H : CMatrix a) (hH : H.IsHermitian) {X : CMatrix a}
    (hX : X.PosSemidef) :
    (spectralSignBlockMatrix H hH X).PosSemidef := by
  unfold spectralSignBlockMatrix hermitianEigenbasisConjugate
  exact (hX.conjTranspose_mul_mul_same (hH.eigenvectorUnitary : CMatrix a)).submatrix _

private theorem spectralSignBlockMatrix_mul
    (H : CMatrix a) (hH : H.IsHermitian) (X Y : CMatrix a) :
    spectralSignBlockMatrix H hH (X * Y) =
      spectralSignBlockMatrix H hH X * spectralSignBlockMatrix H hH Y := by
  let U : CMatrix a := hH.eigenvectorUnitary
  let e := spectralSignIndexEquiv H hH
  change Matrix.reindexAlgEquiv ℂ ℂ e.symm (star U * (X * Y) * U) =
    Matrix.reindexAlgEquiv ℂ ℂ e.symm (star U * X * U) *
      Matrix.reindexAlgEquiv ℂ ℂ e.symm (star U * Y * U)
  rw [show star U * (X * Y) * U = (star U * X * U) * (star U * Y * U) by
    have hU : U * star U = 1 := by simp [U]
    calc
      star U * (X * Y) * U = star U * X * (Y * U) := by noncomm_ring
      _ = star U * X * (U * star U) * Y * U := by rw [hU]; noncomm_ring
      _ = (star U * X * U) * (star U * Y * U) := by noncomm_ring]
  exact Matrix.reindexAlgEquiv_mul (R := ℂ) (A := ℂ) e.symm
    (star U * X * U) (star U * Y * U)

private theorem spectralSignBlockMatrix_sub
    (H : CMatrix a) (hH : H.IsHermitian) (X Y : CMatrix a) :
    spectralSignBlockMatrix H hH (X - Y) =
      spectralSignBlockMatrix H hH X - spectralSignBlockMatrix H hH Y := by
  unfold spectralSignBlockMatrix hermitianEigenbasisConjugate
  ext i j
  simp [Matrix.mul_sub, Matrix.sub_mul]

private theorem spectralSignBlockMatrix_smul
    (H : CMatrix a) (hH : H.IsHermitian) (c : ℝ) (X : CMatrix a) :
    spectralSignBlockMatrix H hH (c • X) =
      c • spectralSignBlockMatrix H hH X := by
  unfold spectralSignBlockMatrix hermitianEigenbasisConjugate
  ext i j
  simp

private theorem hermitianEigenbasisConjugate_self
    (H : CMatrix a) (hH : H.IsHermitian) :
    hermitianEigenbasisConjugate H hH H =
      Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := by
  let U : CMatrix a := hH.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => ((hH.eigenvalues i : ℝ) : ℂ)
  have hHdiag : H = U * D * star U := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hH.spectral_theorem
  unfold hermitianEigenbasisConjugate
  change star U * H * U = D
  rw [hHdiag]
  have hU : star U * U = 1 := by simp [U]
  calc
    star U * (U * D * star U) * U = (star U * U) * D * (star U * U) := by
      noncomm_ring
    _ = 1 * D * 1 := by rw [hU]
    _ = D := by simp

private theorem hermitianEigenbasisConjugate_projector
    (H : CMatrix a) (hH : H.IsHermitian) :
    hermitianEigenbasisConjugate H hH (positiveSpectralProjector H hH) =
      Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0) := by
  unfold positiveSpectralProjector hermitianEigenbasisConjugate
  let U : CMatrix a := hH.eigenvectorUnitary
  let D : CMatrix a :=
    Matrix.diagonal fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0
  have hU : star U * U = 1 := by simp [U]
  change star U * (U * D * star U) * U = D
  calc
    star U * (U * D * star U) * U = (star U * U) * D * (star U * U) := by
      noncomm_ring
    _ = 1 * D * 1 := by rw [hU]
    _ = D := by simp

private theorem spectralSignBlockMatrix_self
    (H : CMatrix a) (hH : H.IsHermitian) :
    spectralSignBlockMatrix H hH H =
      Matrix.fromBlocks (positiveEigenvalueBlock H hH) 0 0
        (-(negativeEigenvalueBlock H hH)) := by
  classical
  ext x y
  rcases x with i | i <;> rcases y with j | j
  · unfold spectralSignBlockMatrix positiveEigenvalueBlock
    rw [hermitianEigenbasisConjugate_self]
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal, spectralSignIndexEquiv, Equiv.sumCompl_apply_inl]
    · have hval : (i : a) ≠ (j : a) := by intro h; exact hij (Subtype.ext h)
      simp [Matrix.diagonal, spectralSignIndexEquiv, Equiv.sumCompl_apply_inl, hij, hval]
  · unfold spectralSignBlockMatrix positiveEigenvalueBlock negativeEigenvalueBlock
    rw [hermitianEigenbasisConjugate_self]
    by_cases hval : (i : a) = (j : a)
    · exfalso
      exact j.2 (hval ▸ i.2)
    · simp [Matrix.diagonal, spectralSignIndexEquiv, Equiv.sumCompl_apply_inl,
        Equiv.sumCompl_apply_inr, hval]
  · unfold spectralSignBlockMatrix positiveEigenvalueBlock negativeEigenvalueBlock
    rw [hermitianEigenbasisConjugate_self]
    by_cases hval : (i : a) = (j : a)
    · exfalso
      exact i.2 (hval ▸ j.2)
    · simp [Matrix.diagonal, spectralSignIndexEquiv, Equiv.sumCompl_apply_inl,
        Equiv.sumCompl_apply_inr, hval]
  · unfold spectralSignBlockMatrix negativeEigenvalueBlock
    rw [hermitianEigenbasisConjugate_self]
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal, spectralSignIndexEquiv, Equiv.sumCompl_apply_inr]
    · have hval : (i : a) ≠ (j : a) := by
        intro h
        exact hij (Subtype.ext h)
      simp [Matrix.diagonal, spectralSignIndexEquiv, Equiv.sumCompl_apply_inr, hij, hval]

private theorem spectralSignBlockMatrix_projector
    (H : CMatrix a) (hH : H.IsHermitian) :
    spectralSignBlockMatrix H hH (positiveSpectralProjector H hH) =
      Matrix.fromBlocks (1 : CMatrix (positiveSpectralIndex H hH)) 0 0
        (0 : CMatrix (nonpositiveSpectralIndex H hH)) := by
  classical
  ext x y
  rcases x with i | i <;> rcases y with j | j
  · unfold spectralSignBlockMatrix
    rw [hermitianEigenbasisConjugate_projector]
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal, spectralSignIndexEquiv, Equiv.sumCompl_apply_inl, i.2]
    · have hval : (i : a) ≠ (j : a) := by intro h; exact hij (Subtype.ext h)
      simp [Matrix.diagonal, spectralSignIndexEquiv, Equiv.sumCompl_apply_inl, hij, hval]
  · unfold spectralSignBlockMatrix
    rw [hermitianEigenbasisConjugate_projector]
    by_cases hval : (i : a) = (j : a)
    · exfalso
      exact j.2 (hval ▸ i.2)
    · simp [Matrix.diagonal, spectralSignIndexEquiv, Equiv.sumCompl_apply_inl,
        Equiv.sumCompl_apply_inr, hval]
  · unfold spectralSignBlockMatrix
    rw [hermitianEigenbasisConjugate_projector]
    by_cases hval : (i : a) = (j : a)
    · exfalso
      exact i.2 (hval ▸ j.2)
    · simp [Matrix.diagonal, spectralSignIndexEquiv, Equiv.sumCompl_apply_inl,
        Equiv.sumCompl_apply_inr, hval]
  · unfold spectralSignBlockMatrix
    rw [hermitianEigenbasisConjugate_projector]
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal, spectralSignIndexEquiv, Equiv.sumCompl_apply_inr, i.2]
    · have hval : (i : a) ≠ (j : a) := by intro h; exact hij (Subtype.ext h)
      simp [Matrix.diagonal, spectralSignIndexEquiv, Equiv.sumCompl_apply_inr, hval]

omit [DecidableEq a] in
private theorem sumBlock11_fromBlocks_left_mul
    {p : Type u} {n : Type v} [Fintype p] [Fintype n]
    (A : Matrix p p ℂ) (D : Matrix n n ℂ)
    (M : Matrix (Sum p n) (Sum p n) ℂ) :
    Matrix.sumBlock11 (Matrix.fromBlocks A 0 0 D * M) =
      A * Matrix.sumBlock11 M := by
  ext i j
  simp [Matrix.sumBlock11, Matrix.mul_apply, Fintype.sum_sum_type]

private theorem trace_fromBlocks_projector_mul
    {p : Type u} {n : Type v} [Fintype p] [DecidableEq p] [Fintype n]
    (M : Matrix (Sum p n) (Sum p n) ℂ) :
    (Matrix.fromBlocks (1 : Matrix p p ℂ) 0 0 (0 : Matrix n n ℂ) * M).trace =
      (Matrix.sumBlock11 M).trace := by
  rw [← Matrix.fromBlocks_sumBlocks M]
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.trace]

private theorem positiveSpectralProjector_trace_mul
    (H : CMatrix a) (hH : H.IsHermitian) (X : CMatrix a) :
    (positiveSpectralProjector H hH * X).trace =
      (Matrix.sumBlock11 (spectralSignBlockMatrix H hH X)).trace := by
  rw [← spectralSignBlockMatrix_trace H hH
    (positiveSpectralProjector H hH * X)]
  rw [spectralSignBlockMatrix_mul, spectralSignBlockMatrix_projector]
  exact trace_fromBlocks_projector_mul _

private theorem trace_mul_le_of_le {D X Y : CMatrix a}
    (hD : D.PosSemidef) (hXY : X ≤ Y) :
    ((D * X).trace).re ≤ ((D * Y).trace).re := by
  rw [Matrix.le_iff] at hXY
  have hnonneg := cMatrix_trace_mul_posSemidef_re_nonneg hD hXY
  have hcalc : ((D * (Y - X)).trace).re =
      ((D * Y).trace).re - ((D * X).trace).re := by
    simp [Matrix.mul_sub, Matrix.trace_sub]
  linarith

/-- Real powers of positive semidefinite matrices are positive semidefinite. -/
public theorem cMatrix_rpow_posSemidef {s : ℝ} {A : CMatrix a}
    (_hA : A.PosSemidef) :
    (CFC.rpow A s).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := A) (y := s))

/-- The left-half substitution used in Audenaert's proof of Theorem 1. -/
public theorem audenaertLeftHalfParams {s : ℝ}
    (hsPos : 0 < s) (hsHalf : s ≤ 1 / 2) :
    let r : ℝ := 1 - s
    let t : ℝ := s / r
    0 < r ∧ 0 ≤ t ∧ t ≤ 1 ∧ r * t = s := by
  dsimp
  have hs_lt_one : s < 1 := lt_of_le_of_lt hsHalf (by norm_num)
  have hr : 0 < 1 - s := sub_pos.mpr hs_lt_one
  have ht_nonneg : 0 ≤ s / (1 - s) := div_nonneg hsPos.le hr.le
  have ht_le : s / (1 - s) ≤ 1 := by
    rw [div_le_one₀ hr]
    linarith
  have hmul : (1 - s) * (s / (1 - s)) = s := by
    field_simp [ne_of_gt hr]
  exact ⟨hr, ht_nonneg, ht_le, hmul⟩

/-- Power-of-power reduction for possibly singular PSD matrices and nonnegative exponents. -/
public theorem cMatrix_rpow_rpow_of_nonneg {A : CMatrix a} (hA : A.PosSemidef)
    {r t s : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) (hrt : r * t = s) :
    CFC.rpow (CFC.rpow A r) t = CFC.rpow A s := by
  rw [show CFC.rpow (CFC.rpow A r) t = CFC.rpow A (r * t) by
    exact CFC.rpow_rpow_of_exponent_nonneg A r t hr ht
      (Matrix.nonneg_iff_posSemidef.mpr hA)]
  rw [hrt]

/-- Positive real powers with exponents adding to one multiply back to a PSD matrix.

This uses the non-unital `nnrpow_add` route, avoiding invertibility assumptions. -/
public theorem cMatrix_rpow_mul_rpow_of_pos_add_eq_one {A : CMatrix a}
    (hA : A.PosSemidef) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r + s = 1) :
    CFC.rpow A r * CFC.rpow A s = A := by
  let rNN : ℝ≥0 := ⟨r, hr.le⟩
  let sNN : ℝ≥0 := ⟨s, hs.le⟩
  have hrNN : 0 < rNN := by exact_mod_cast hr
  have hsNN : 0 < sNN := by exact_mod_cast hs
  have hsum : rNN + sNN = 1 := by
    ext
    exact hrs
  have hadd : A ^ (rNN + sNN) = A ^ rNN * A ^ sNN :=
    CFC.nnrpow_add (a := A) hrNN hsNN
  have hrpow : A ^ rNN = CFC.rpow A r := by
    simpa [rNN] using (CFC.nnrpow_eq_rpow (a := A) hrNN)
  have hspow : A ^ sNN = CFC.rpow A s := by
    simpa [sNN] using (CFC.nnrpow_eq_rpow (a := A) hsNN)
  calc
    CFC.rpow A r * CFC.rpow A s = A ^ rNN * A ^ sNN := by rw [← hrpow, ← hspow]
    _ = A ^ (rNN + sNN) := hadd.symm
    _ = A ^ (1 : ℝ≥0) := by rw [hsum]
    _ = A := CFC.nnrpow_one A (Matrix.nonneg_iff_posSemidef.mpr hA)

/-- The positive spectral projector selects the positive part on the left. -/
public theorem positiveSpectralProjector_mul_self_eq_posPart
    (H : CMatrix a) (hH : H.IsHermitian) :
    positiveSpectralProjector H hH * H = H⁺ := by
  have hsub : H⁺ - H⁻ = H := CFC.posPart_sub_negPart H hH.isSelfAdjoint
  calc
    positiveSpectralProjector H hH * H =
        positiveSpectralProjector H hH * (H⁺ - H⁻) := by rw [hsub]
    _ = positiveSpectralProjector H hH * H⁺ -
        positiveSpectralProjector H hH * H⁻ := by rw [mul_sub]
    _ = H⁺ - 0 := by
          rw [positiveSpectralProjector_mul_posPart,
            positiveSpectralProjector_mul_negPart]
    _ = H⁺ := by simp

/-- Trace-max upper bound for any effect against a Hermitian matrix. -/
public theorem trace_mul_le_trace_mul_posPart
    (P H : CMatrix a) (hPpos : P.PosSemidef) (hPle : P ≤ 1)
    (hH : H.IsHermitian) :
    ((P * H).trace).re ≤ (H⁺).trace.re := by
  rw [Matrix.trace_mul_comm]
  exact hermitian_trace_mul_effect_le_posPart_trace H P hH hPpos hPle

private theorem one_sub_positiveSpectralProjector_mul_neg_self_eq_negPart
    (H : CMatrix a) (hH : H.IsHermitian) :
    (1 - positiveSpectralProjector H hH) * (-H) = H⁻ := by
  let P := positiveSpectralProjector H hH
  have hPH : P * H = H⁺ := positiveSpectralProjector_mul_self_eq_posPart H hH
  have hsub : H⁺ - H⁻ = H := CFC.posPart_sub_negPart H hH.isSelfAdjoint
  have hQH : (1 - P) * H = -H⁻ := by
    calc
      (1 - P) * H = H - P * H := by simp [sub_mul]
      _ = H - H⁺ := by rw [hPH]
      _ = -H⁻ := by
        nth_rewrite 1 [← hsub]
        abel
  calc
    (1 - P) * (-H) = -((1 - P) * H) := by rw [mul_neg]
    _ = -(-H⁻) := by rw [hQH]
    _ = H⁻ := by simp

/-- Complementary-projector estimate used in the left-half proof of Audenaert Theorem 1. -/
public theorem audenaertComplementProjector_trace_ge
    {s : ℝ} (_hs0 : 0 ≤ s)
    {A X Y : CMatrix a}
    (hA : A.PosSemidef) (_hX : X.PosSemidef) (_hY : Y.PosSemidef)
    (hXY : (X - Y).IsHermitian)
    (hXA : X * CFC.rpow A s = A) :
    let P : CMatrix a := positiveSpectralProjector (X - Y) hXY
    (((1 - P) * Y * CFC.rpow A s).trace).re ≥
      (((1 - P) * A).trace).re := by
  dsimp
  let H : CMatrix a := X - Y
  let P : CMatrix a := positiveSpectralProjector H hXY
  let R : CMatrix a := CFC.rpow A s
  have hR : R.PosSemidef := cMatrix_rpow_posSemidef hA
  have hQYX : ((1 - P) * (Y - X)).PosSemidef := by
    have hEq : (1 - P) * (Y - X) = H⁻ := by
      simpa [H, P, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        one_sub_positiveSpectralProjector_mul_neg_self_eq_negPart H hXY
    rw [hEq]
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H)
  have hnonneg : 0 ≤ (((1 - P) * (Y - X) * R).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg hQYX hR
  have htrace :
      (((1 - P) * (Y - X) * R).trace).re =
        (((1 - P) * Y * R).trace).re - (((1 - P) * A).trace).re := by
    have hXA' : X * R = A := by simpa [R] using hXA
    rw [← hXA']
    simp [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_assoc]
  simpa [P, H, R] using (sub_nonneg.mp (by linarith : 0 ≤
    (((1 - P) * Y * R).trace).re - (((1 - P) * A).trace).re))

/-- Source-shaped right-hand side rewritten through the positive part. -/
public theorem audenaertTraceAbsRhs_eq_trace_sub_posPart
    {A B : CMatrix a} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ((A + B - CFC.abs (A - B)).trace).re / 2 =
      A.trace.re - ((A - B)⁺).trace.re := by
  let H : CMatrix a := A - B
  have hH : H.IsHermitian := hA.isHermitian.sub hB.isHermitian
  have hAbs : H⁺ + H⁻ = CFC.abs H :=
    CFC.posPart_add_negPart H hH.isSelfAdjoint
  have hSub : H⁺ - H⁻ = H :=
    CFC.posPart_sub_negPart H hH.isSelfAdjoint
  have htrace_abs :
      (CFC.abs H).trace.re = (H⁺).trace.re + (H⁻).trace.re := by
    have h := congrArg Complex.re (congrArg Matrix.trace hAbs)
    simpa [Matrix.trace_add] using h.symm
  have htrace_sub :
      (H⁺).trace.re - (H⁻).trace.re = A.trace.re - B.trace.re := by
    have h := congrArg Complex.re (congrArg Matrix.trace hSub)
    simpa [H, Matrix.trace_sub] using h
  have hsource :
      ((A + B - CFC.abs (A - B)).trace).re / 2 =
        (A.trace.re + B.trace.re - ((A - B)⁺).trace.re -
          ((A - B)⁻).trace.re) / 2 := by
    simp [Matrix.trace_add, Matrix.trace_sub, htrace_abs, H]
    ring
  rw [hsource]
  linarith

/-- Cyclicity of trace for the Audenaert trace product's real part. -/
public theorem audenaertTraceProduct_comm_re {A B : CMatrix a} {s : ℝ} :
    ((CFC.rpow A s * CFC.rpow B (1 - s)).trace).re =
      ((CFC.rpow B (1 - s) * CFC.rpow A s).trace).re := by
  rw [Matrix.trace_mul_comm]

/-- The `CFC.abs` right-hand side is invariant under swapping the two operators. -/
public theorem audenaertTraceAbsRhs_swap (A B : CMatrix a) :
    CFC.abs (B - A) = CFC.abs (A - B) := by
  have hneg : B - A = -(A - B) := by
    abel
  rw [hneg, CFC.abs_neg]

private noncomputable def traceLeftRightCLM (P B : CMatrix a) :
    CMatrix a →L[ℝ] ℝ :=
  Complex.reCLM.comp (LinearMap.toContinuousLinearMap ({
    toFun := fun X : CMatrix a => ((P * B * X).trace)
    map_add' := by
      intro X Y
      simp [Matrix.mul_add, Matrix.trace_add]
    map_smul' := by
      intro c X
      simp [Matrix.trace_smul]
  } : CMatrix a →ₗ[ℝ] ℂ))

private theorem traceLeftRightCLM_apply (P B X : CMatrix a) :
    traceLeftRightCLM P B X = ((P * B * X).trace).re :=
  rfl

/-- Left/right multiplication and trace commute with interval Bochner integrals. -/
public theorem audenaertTraceLeftRight_intervalIntegral
    {f : ℝ → CMatrix a} (hf : IntervalIntegrable f volume (0 : ℝ) 1)
    (P B : CMatrix a) :
    ((P * B * (∫ u in (0 : ℝ)..1, f u)).trace).re =
      ∫ u in (0 : ℝ)..1, ((P * B * f u).trace).re := by
  simpa [traceLeftRightCLM] using
    ((traceLeftRightCLM P B).intervalIntegral_comp_comm
      (μ := volume) (a := (0 : ℝ)) (b := 1) hf).symm

/-- Left/right multiplication and trace commute with Bochner integrals over a measurable set. -/
public theorem audenaertTraceLeftRight_setIntegral
    {μ : Measure ℝ} {s : Set ℝ} {f : ℝ → CMatrix a}
    (hf : IntegrableOn f s μ) (P B : CMatrix a) :
    ((P * B * (∫ r in s, f r ∂μ)).trace).re =
      ∫ r in s, ((P * B * f r).trace).re ∂μ := by
  simpa [traceLeftRightCLM, IntegrableOn] using
    ((traceLeftRightCLM P B).integral_comp_comm (μ := μ.restrict s) hf).symm

/-- Integrability of the scalar trace integrand obtained from two matrix integrands. -/
public theorem audenaertTraceLeftRight_sub_integrableOn
    {μ : Measure ℝ} {s : Set ℝ} {f g : ℝ → CMatrix a}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
    (P B : CMatrix a) :
    IntegrableOn (fun r : ℝ => ((P * B * (f r - g r)).trace).re) s μ := by
  have hdiff : IntegrableOn (fun r : ℝ => f r - g r) s μ := hf.sub hg
  simpa [traceLeftRightCLM, IntegrableOn, Matrix.mul_sub, Matrix.trace_sub] using
    (traceLeftRightCLM P B).integrable_comp hdiff

omit [DecidableEq a] in
private theorem sumBlock11_mul_self
    {p : Type u} {n : Type v} [Fintype p] [Fintype n]
    (S : Matrix (Sum p n) (Sum p n) ℂ) :
    Matrix.sumBlock11 (S * S) =
      Matrix.sumBlock11 S * Matrix.sumBlock11 S +
        Matrix.sumBlock12 S * Matrix.sumBlock21 S := by
  ext i j
  simp [Matrix.sumBlock11, Matrix.sumBlock12, Matrix.sumBlock21,
    Matrix.mul_apply, Fintype.sum_sum_type]

omit [DecidableEq a] in
private theorem sumBlock11_mul_diag_mul
    {p : Type u} {n : Type v} [Fintype p] [Fintype n]
    (Dp : Matrix p p ℂ) (Dn : Matrix n n ℂ)
    (S : Matrix (Sum p n) (Sum p n) ℂ) :
    Matrix.sumBlock11 (S * Matrix.fromBlocks Dp 0 0 (-Dn) * S) =
      Matrix.sumBlock11 S * Dp * Matrix.sumBlock11 S -
        Matrix.sumBlock12 S * Dn * Matrix.sumBlock21 S := by
  ext i j
  simp [Matrix.sumBlock11, Matrix.sumBlock12, Matrix.sumBlock21,
    Matrix.mul_apply, Fintype.sum_sum_type, Finset.sum_mul, sub_eq_add_neg]

omit [DecidableEq a] in
private theorem terminal_block_algebra
    {p : Type u} {n : Type v} [Fintype p] [Fintype n]
    (Dp : Matrix p p ℂ) (Dn : Matrix n n ℂ)
    (S : Matrix (Sum p n) (Sum p n) ℂ) :
    (Dp * Matrix.sumBlock11 (S * S) -
        Matrix.sumBlock11 (S * Matrix.fromBlocks Dp 0 0 (-Dn) * S)).trace =
      (Dp * Matrix.sumBlock12 S * Matrix.sumBlock21 S +
        Matrix.sumBlock12 S * Dn * Matrix.sumBlock21 S).trace := by
  rw [sumBlock11_mul_self, sumBlock11_mul_diag_mul]
  simp [Matrix.mul_add, Matrix.trace_add, Matrix.trace_sub]
  rw [show (Dp * (Matrix.sumBlock11 S * Matrix.sumBlock11 S)).trace =
      (Matrix.sumBlock11 S * (Matrix.sumBlock11 S * Dp)).trace by
    rw [Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]]
  rw [show (Matrix.sumBlock11 S * (Matrix.sumBlock11 S * Dp)).trace =
      (Matrix.sumBlock11 S * Dp * Matrix.sumBlock11 S).trace by
    rw [Matrix.trace_mul_comm]]
  simp [Matrix.mul_assoc]

/-- Positivity of the conjugated `B` term in Audenaert's Appendix A path argument. -/
public theorem audenaertPathResolvent_mul_B_mul_resolvent_posSemidef {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    {u r : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hr : 0 < r) :
    (audenaertPathResolvent A B u r * B *
      audenaertPathResolvent A B u r).PosSemidef := by
  have hV := audenaertPathResolvent_isHermitian hA hB hu0 hu1 hr
  simpa [hV.eq] using
    hB.conjTranspose_mul_mul_same (audenaertPathResolvent A B u r)

/-- The `V * B * V` identity behind the positive-block matrix-order step. -/
public theorem audenaertPathResolvent_mul_B_mul_resolvent_eq {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    {u r : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hr : 0 < r) :
    audenaertPathResolvent A B u r * B * audenaertPathResolvent A B u r =
      audenaertPathResolvent A B u r -
        u • (audenaertPathResolvent A B u r * (A - B) *
          audenaertPathResolvent A B u r) -
        r • (audenaertPathResolvent A B u r *
          audenaertPathResolvent A B u r) := by
  let C : CMatrix a := audenaertPathMatrix A B u
  let V : CMatrix a := audenaertPathResolvent A B u r
  have hunit := audenaertPathResolvent_isUnit hA hB hu0 hu1 hr
  have hdet : IsUnit (C + r • (1 : CMatrix a)).det := by
    exact (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hleft : V * (C + r • (1 : CMatrix a)) = 1 := by
    simpa [V, C, audenaertPathResolvent] using
      Matrix.nonsing_inv_mul (C + r • (1 : CMatrix a)) hdet
  have hBexpr : C - u • (A - B) = B := by
    ext i j
    simp [C, audenaertPathMatrix, sub_eq_add_neg, smul_add]
    ring
  have hVCV : V * C * V = V - r • (V * V) := by
    calc
      V * C * V = V * ((C + r • (1 : CMatrix a)) - r • (1 : CMatrix a)) * V := by
        simp
      _ = (V * (C + r • (1 : CMatrix a))) * V -
          (V * (r • (1 : CMatrix a))) * V := by
        rw [mul_sub, sub_mul]
      _ = V - r • (V * V) := by
        rw [hleft]
        simp
  calc
    V * B * V = V * (C - u • (A - B)) * V := by rw [hBexpr]
    _ = V * C * V - (V * (u • (A - B))) * V := by
      rw [mul_sub, sub_mul]
    _ = (V - r • (V * V)) - u • (V * (A - B) * V) := by
      rw [hVCV]
      simp [mul_assoc]
    _ = V - u • (V * (A - B) * V) - r • (V * V) := by
      abel

/-- The positive block inequality extracted from `V * B * V ≥ 0`. -/
public theorem audenaertPathResolvent_positiveBlock_le {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    {u r : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hr : 0 < r) :
    r • Matrix.sumBlock11
        (spectralSignBlockMatrix (A - B) (hA.isHermitian.sub hB.isHermitian)
          (audenaertPathResolvent A B u r * audenaertPathResolvent A B u r)) ≤
      Matrix.sumBlock11
        (spectralSignBlockMatrix (A - B) (hA.isHermitian.sub hB.isHermitian)
          (audenaertPathResolvent A B u r -
            u • (audenaertPathResolvent A B u r * (A - B) *
              audenaertPathResolvent A B u r))) := by
  let H : CMatrix a := A - B
  let hH : H.IsHermitian := hA.isHermitian.sub hB.isHermitian
  let V : CMatrix a := audenaertPathResolvent A B u r
  rw [Matrix.le_iff]
  have hVBV : (V * B * V).PosSemidef := by
    simpa [V] using
      audenaertPathResolvent_mul_B_mul_resolvent_posSemidef hA hB hu0 hu1 hr
  have hblock : (spectralSignBlockMatrix H hH (V * B * V)).PosSemidef :=
    spectralSignBlockMatrix_posSemidef H hH hVBV
  have h11 : (Matrix.sumBlock11 (spectralSignBlockMatrix H hH (V * B * V))).PosSemidef :=
    Matrix.sumBlock11_posSemidef hblock
  have hiden : V * B * V = V - u • (V * H * V) - r • (V * V) := by
    simpa [V, H] using
      audenaertPathResolvent_mul_B_mul_resolvent_eq hA hB hu0 hu1 hr
  have hdiff :
      Matrix.sumBlock11 (spectralSignBlockMatrix H hH (V - u • (V * H * V))) -
          r • Matrix.sumBlock11 (spectralSignBlockMatrix H hH (V * V)) =
        Matrix.sumBlock11 (spectralSignBlockMatrix H hH (V * B * V)) := by
    rw [hiden]
    ext i j
    simp [spectralSignBlockMatrix, hermitianEigenbasisConjugate, Matrix.sumBlock11,
      sub_eq_add_neg, Matrix.mul_add, Matrix.add_mul]
  simpa [H, hH, V, hdiff]

private theorem audenaertPath_B_mul_VHV_eq {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    {u r : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hr : 0 < r) :
    let H : CMatrix a := A - B
    let V : CMatrix a := audenaertPathResolvent A B u r
    B * (V * H * V) =
      H * V - u • (H * (V * H * V)) - r • (V * H * V) := by
  intro H V
  let C : CMatrix a := audenaertPathMatrix A B u
  have hunit := audenaertPathResolvent_isUnit hA hB hu0 hu1 hr
  have hdet : IsUnit (C + r • (1 : CMatrix a)).det := by
    exact (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hleft : (C + r • (1 : CMatrix a)) * V = 1 := by
    simpa [V, C, audenaertPathResolvent] using
      Matrix.mul_nonsing_inv (C + r • (1 : CMatrix a)) hdet
  have hBexpr : B = C - u • H := by
    ext i j
    simp [C, H, audenaertPathMatrix, sub_eq_add_neg, smul_add]
    ring
  calc
    B * (V * H * V) = (C - u • H) * (V * H * V) := by rw [hBexpr]
    _ = C * (V * H * V) - (u • H) * (V * H * V) := by rw [sub_mul]
    _ = ((C + r • (1 : CMatrix a)) - r • (1 : CMatrix a)) * (V * H * V) -
          (u • H) * (V * H * V) := by simp
    _ = (C + r • (1 : CMatrix a)) * (V * H * V) -
          (r • (1 : CMatrix a)) * (V * H * V) -
          (u • H) * (V * H * V) := by rw [sub_mul]
    _ = H * V - r • (V * H * V) - u • (H * (V * H * V)) := by
      calc
        (C + r • (1 : CMatrix a)) * (V * H * V) -
              (r • (1 : CMatrix a)) * (V * H * V) -
              (u • H) * (V * H * V)
            = ((C + r • (1 : CMatrix a)) * V) * H * V -
              r • (V * H * V) - u • (H * (V * H * V)) := by
                simp [mul_assoc]
        _ = H * V - r • (V * H * V) - u • (H * (V * H * V)) := by
          rw [hleft]
          simp [mul_assoc]
    _ = H * V - u • (H * (V * H * V)) - r • (V * H * V) := by abel

/-- Audenaert's Appendix A lower-bound step before applying terminal positivity. -/
public theorem audenaertResolventPath_trace_ge_terminal {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    {u r : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hr : 0 < r) :
    r * ((appendixATerminalOriginal (A - B)
          (audenaertPathResolvent A B u r)
          (hA.isHermitian.sub hB.isHermitian)).trace).re ≤
      (((positiveSpectralProjector (A - B)
          (hA.isHermitian.sub hB.isHermitian)) * B *
        (audenaertPathResolvent A B u r * (A - B) *
          audenaertPathResolvent A B u r)).trace).re := by
  let H : CMatrix a := A - B
  let hH : H.IsHermitian := hA.isHermitian.sub hB.isHermitian
  let V : CMatrix a := audenaertPathResolvent A B u r
  let S := spectralSignBlockMatrix H hH V
  let Dp := positiveEigenvalueBlock H hH
  let Dn := negativeEigenvalueBlock H hH
  let D : CMatrix (Sum (positiveSpectralIndex H hH) (nonpositiveSpectralIndex H hH)) :=
    Matrix.fromBlocks Dp 0 0 (-Dn)
  let Y := Matrix.sumBlock11 (S - u • (S * D * S))
  let W := Matrix.sumBlock11 (S * S)
  let Z := Matrix.sumBlock11 (S * D * S)
  have hVh : V.IsHermitian := audenaertPathResolvent_isHermitian hA hB hu0 hu1 hr
  have hterminal :
      ((appendixATerminalOriginal H V hH).trace).re =
        ((Dp * Matrix.sumBlock12 S * Matrix.sumBlock21 S +
          Matrix.sumBlock12 S * Dn * Matrix.sumBlock21 S).trace).re := by
    simpa [H, hH, V, S, Dp, Dn] using
      appendixATerminalOriginal_trace_eq_block H V hH hVh
  have hterminalAlg :
      ((Dp * W - Z).trace).re =
        ((appendixATerminalOriginal H V hH).trace).re := by
    have h := terminal_block_algebra Dp Dn S
    simpa [W, Z, D, hterminal] using congrArg Complex.re h
  have horder : r • W ≤ Y := by
    have hraw := audenaertPathResolvent_positiveBlock_le hA hB hu0 hu1 hr
    simpa [H, hH, V, S, D, Y, W, spectralSignBlockMatrix_mul,
      spectralSignBlockMatrix_sub, spectralSignBlockMatrix_smul,
      spectralSignBlockMatrix_self] using hraw
  have horderTrace : r * ((Dp * W).trace).re ≤ ((Dp * Y).trace).re := by
    have h := trace_mul_le_of_le (positiveEigenvalueBlock_posSemidef H hH) horder
    simpa [Matrix.trace_smul] using h
  have hblockTrace :
      ((Matrix.sumBlock11
        (spectralSignBlockMatrix H hH (B * (V * H * V)))).trace).re =
        ((Dp * Y - r • Z).trace).re := by
    have hBV : B * (V * H * V) =
        H * V - u • (H * (V * H * V)) - r • (V * H * V) := by
      simpa [H, V] using audenaertPath_B_mul_VHV_eq hA hB hu0 hu1 hr
    rw [hBV]
    rw [spectralSignBlockMatrix_sub, spectralSignBlockMatrix_sub,
      spectralSignBlockMatrix_smul, spectralSignBlockMatrix_smul]
    rw [spectralSignBlockMatrix_mul, spectralSignBlockMatrix_mul,
      spectralSignBlockMatrix_mul, spectralSignBlockMatrix_mul]
    rw [spectralSignBlockMatrix_self]
    change
      ((Matrix.sumBlock11
        (D * S - u • (D * (S * D * S)) - r • (S * D * S))).trace).re =
        ((Dp * Y - r • Z).trace).re
    have hsum :
        Matrix.sumBlock11
          (D * S - u • (D * (S * D * S)) - r • (S * D * S)) =
          Dp * Y - r • Z := by
      have hsplit :
          Matrix.sumBlock11
              (D * S - u • (D * (S * D * S)) - r • (S * D * S)) =
            Matrix.sumBlock11 (D * S) -
              u • Matrix.sumBlock11 (D * (S * D * S)) -
              r • Matrix.sumBlock11 (S * D * S) := by
        ext i j
        simp [Matrix.sumBlock11]
      rw [hsplit]
      rw [sumBlock11_fromBlocks_left_mul Dp (-Dn) S]
      rw [sumBlock11_fromBlocks_left_mul Dp (-Dn) (S * D * S)]
      have hY : Y = Matrix.sumBlock11 S - u • Z := by
        ext i j
        simp [Y, Z, Matrix.sumBlock11]
      rw [hY]
      change Dp * Matrix.sumBlock11 S - u • (Dp * Z) - r • Z =
        Dp * (Matrix.sumBlock11 S - u • Z) - r • Z
      rw [Matrix.mul_sub]
      simp
    rw [hsum]
  have hmain :
      r * ((appendixATerminalOriginal H V hH).trace).re ≤
        ((Dp * Y - r • Z).trace).re := by
    rw [← hterminalAlg]
    have hleft :
        r * ((Dp * W - Z).trace).re =
          r * ((Dp * W).trace).re - r * (Z.trace).re := by
      simp [Matrix.trace_sub]
      ring
    have hright :
        ((Dp * Y - r • Z).trace).re =
          ((Dp * Y).trace).re - r * (Z.trace).re := by
      simp [Matrix.trace_sub, Matrix.trace_smul]
    rw [hleft, hright]
    linarith
  have hptrace :
      (((positiveSpectralProjector H hH) * B * (V * H * V)).trace).re =
        ((Dp * Y - r • Z).trace).re := by
    calc
      (((positiveSpectralProjector H hH) * B * (V * H * V)).trace).re =
          (((positiveSpectralProjector H hH) * (B * (V * H * V))).trace).re := by
            simp [Matrix.mul_assoc]
      _ = ((Matrix.sumBlock11
            (spectralSignBlockMatrix H hH (B * (V * H * V)))).trace).re := by
            exact congrArg Complex.re
              (positiveSpectralProjector_trace_mul H hH (B * (V * H * V)))
      _ = ((Dp * Y - r • Z).trace).re := hblockTrace
  simpa [H, hH, V] using hmain.trans_eq hptrace.symm

/-- Nonnegativity of the derivative trace integrand in the path-calculus bridge. -/
public theorem audenaertResolventPath_derivative_trace_nonneg {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    {u r : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hr : 0 < r) :
    0 ≤ (((positiveSpectralProjector (A - B)
        (hA.isHermitian.sub hB.isHermitian)) * B *
      (r • (audenaertPathResolvent A B u r * (A - B) *
        audenaertPathResolvent A B u r))).trace).re := by
  let H : CMatrix a := A - B
  let hH : H.IsHermitian := hA.isHermitian.sub hB.isHermitian
  let V : CMatrix a := audenaertPathResolvent A B u r
  let P := positiveSpectralProjector H hH
  have hterm :
      0 ≤ ((appendixATerminalOriginal H V hH).trace).re :=
    positiveSpectralTerminalTrace_original_nonneg H V hH
      (audenaertPathResolvent_isHermitian hA hB hu0 hu1 hr)
  have hge :
      r * ((appendixATerminalOriginal H V hH).trace).re ≤
        ((P * B * (V * H * V)).trace).re := by
    simpa [H, hH, V, P] using
      audenaertResolventPath_trace_ge_terminal hA hB hu0 hu1 hr
  have hbase : 0 ≤ ((P * B * (V * H * V)).trace).re :=
    le_trans (mul_nonneg hr.le hterm) hge
  have hscaled : 0 ≤ r * ((P * B * (V * H * V)).trace).re :=
    mul_nonneg hr.le hbase
  simpa [H, hH, V, P, Matrix.trace_smul] using hscaled

/-- Derivative of Audenaert's path-resolvent map. -/
public theorem audenaertResolventPath_hasDerivAt {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    {u r : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hr : 0 < r) :
    HasDerivAt
      (fun s : ℝ =>
        audenaertPathMatrix A B s *
          (audenaertPathMatrix A B s + r • (1 : CMatrix a))⁻¹)
      (r • (audenaertPathResolvent A B u r * (A - B) *
        audenaertPathResolvent A B u r)) u := by
  let C : ℝ → CMatrix a := fun s => audenaertPathMatrix A B s
  let X : ℝ → CMatrix a := fun s => C s + r • (1 : CMatrix a)
  let V : CMatrix a := audenaertPathResolvent A B u r
  have hC : HasDerivAt C (A - B) u := by
    have hsmul : HasDerivAt (fun s : ℝ => s • (A - B)) (A - B) u := by
      have hid : HasDerivAt (fun s : ℝ => s) (1 : ℝ) u := hasDerivAt_id u
      simpa [one_smul] using (hid.smul_const (A - B))
    change HasDerivAt (fun s : ℝ => B + s • (A - B)) (A - B) u
    exact hsmul.const_add B
  have hX : HasDerivAt X (A - B) u := by
    dsimp [X]
    exact hC.add_const (r • (1 : CMatrix a))
  have hunit := audenaertPathResolvent_isUnit hA hB hu0 hu1 hr
  have hXunit : IsUnit (X u) := by simpa [X, C] using hunit
  have hInvAt :
      HasFDerivAt Ring.inverse
        (-ContinuousLinearMap.mulLeftRight ℝ (CMatrix a)
          (Ring.inverse (X u)) (Ring.inverse (X u))) (X u) := by
    simpa [hXunit.unit_spec, Ring.inverse_unit, ← Matrix.nonsing_inv_eq_ringInverse]
      using (hasFDerivAt_ringInverse (𝕜 := ℝ) hXunit.unit)
  have hInvDeriv : HasDerivAt (fun s : ℝ => (X s)⁻¹)
      (-(V * (A - B) * V)) u := by
    have hcomp : HasDerivAt (Ring.inverse ∘ X)
        ((-ContinuousLinearMap.mulLeftRight ℝ (CMatrix a)
          (Ring.inverse (X u)) (Ring.inverse (X u))) (A - B)) u := by
      exact HasFDerivAt.comp_hasDerivAt (f := X) (x := u) hInvAt hX
    simpa [V, X, C, audenaertPathResolvent, Matrix.nonsing_inv_eq_ringInverse,
      ContinuousLinearMap.mulLeftRight_apply] using hcomp
  have hprod := hC.mul hInvDeriv
  have hdet : IsUnit (X u).det := by
    exact (Matrix.isUnit_iff_isUnit_det _).mp hXunit
  have hright : (C u + r • (1 : CMatrix a)) * V = 1 := by
    simpa [V, X, C, audenaertPathResolvent] using
      Matrix.mul_nonsing_inv (C u + r • (1 : CMatrix a)) hdet
  have hCV : C u * V = 1 - r • V := by
    calc
      C u * V = ((C u + r • (1 : CMatrix a)) - r • (1 : CMatrix a)) * V := by
        simp
      _ = (C u + r • (1 : CMatrix a)) * V - (r • (1 : CMatrix a)) * V := by
        rw [sub_mul]
      _ = 1 - r • V := by rw [hright]; simp
  have hder :
      (A - B) * V + C u * (-(V * (A - B) * V)) =
        r • (V * (A - B) * V) := by
    calc
      (A - B) * V + C u * (-(V * (A - B) * V))
          = (1 - C u * V) * (A - B) * V := by noncomm_ring
      _ = (r • V) * (A - B) * V := by rw [hCV]; simp
      _ = r • (V * (A - B) * V) := by simp [mul_assoc]
  have hder' :
      (A - B) * (X u)⁻¹ + C u * (-(V * (A - B) * V)) =
        r • (V * (A - B) * V) := by
    simpa [V, X, C] using hder
  have hprod' := hprod.congr_deriv hder'
  simpa [C, X, V] using hprod'

/-- The path resolvent is continuous on the unit interval. -/
public theorem audenaertPathResolvent_continuousOn {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun u : ℝ => audenaertPathResolvent A B u r) (Set.uIcc 0 1) := by
  let C : ℝ → CMatrix a := fun s => audenaertPathMatrix A B s
  let X : ℝ → CMatrix a := fun s => C s + r • (1 : CMatrix a)
  have hCdiff : Differentiable ℝ C := by
    intro s
    have hsmul : HasDerivAt (fun t : ℝ => t • (A - B)) (A - B) s := by
      have hid : HasDerivAt (fun t : ℝ => t) (1 : ℝ) s := hasDerivAt_id s
      simpa [one_smul] using (hid.smul_const (A - B))
    have hC : HasDerivAt C (A - B) s := by
      change HasDerivAt (fun t : ℝ => B + t • (A - B)) (A - B) s
      exact hsmul.const_add B
    exact hC.differentiableAt
  have hXdiff : Differentiable ℝ X := by
    intro s
    dsimp [X]
    exact ((hCdiff s).hasDerivAt.add_const (r • (1 : CMatrix a))).differentiableAt
  have hdiff : DifferentiableOn ℝ (fun s : ℝ => Ring.inverse (X s)) (Set.uIcc 0 1) := by
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le zero_le_one] using hs
    have hsunit : IsUnit (X s) := by
      simpa [X, C] using audenaertPathResolvent_isUnit hA hB hsIcc.1 hsIcc.2 hr
    exact ((hXdiff s).inverse hsunit).differentiableWithinAt
  have hcont := hdiff.continuousOn
  simpa [audenaertPathResolvent, X, C, Matrix.nonsing_inv_eq_ringInverse] using hcont

/-- The matrix derivative integrand in Audenaert's path argument is interval-integrable. -/
public theorem audenaertResolventPath_derivative_intervalIntegrable {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {r : ℝ} (hr : 0 < r) :
    IntervalIntegrable
      (fun u : ℝ =>
        r • (audenaertPathResolvent A B u r * (A - B) *
          audenaertPathResolvent A B u r))
      volume (0 : ℝ) 1 := by
  have hcontV := audenaertPathResolvent_continuousOn hA hB hr
  apply ContinuousOn.intervalIntegrable
  exact ContinuousOn.const_smul
    ((hcontV.mul continuousOn_const).mul hcontV) r

/-- The real derivative-trace integrand in Audenaert's path argument is interval-integrable. -/
public theorem audenaertResolventPath_derivative_trace_intervalIntegrable {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {r : ℝ} (hr : 0 < r) :
    IntervalIntegrable
      (fun u : ℝ => (((positiveSpectralProjector (A - B)
          (hA.isHermitian.sub hB.isHermitian)) * B *
        (r • (audenaertPathResolvent A B u r * (A - B) *
          audenaertPathResolvent A B u r))).trace).re)
      volume (0 : ℝ) 1 := by
  let H : CMatrix a := A - B
  let P := positiveSpectralProjector H (hA.isHermitian.sub hB.isHermitian)
  let fp : ℝ → CMatrix a := fun u =>
    r • (audenaertPathResolvent A B u r * H * audenaertPathResolvent A B u r)
  have hcontV := audenaertPathResolvent_continuousOn hA hB hr
  have hcontMatrix : ContinuousOn fp (Set.uIcc (0 : ℝ) 1) := by
    dsimp [fp, H]
    exact ContinuousOn.const_smul ((hcontV.mul continuousOn_const).mul hcontV) r
  have hcontScalar :
      ContinuousOn (fun u : ℝ => traceLeftRightCLM P B (fp u)) (Set.uIcc (0 : ℝ) 1) :=
    (traceLeftRightCLM P B).continuous.comp_continuousOn hcontMatrix
  simpa [traceLeftRightCLM, fp, P, H] using hcontScalar.intervalIntegrable

/-- Fundamental-theorem bridge for the endpoint resolvent difference. -/
public theorem audenaertResolventSub_eq_intervalIntegral {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {r : ℝ} (hr : 0 < r) :
    A * (A + r • (1 : CMatrix a))⁻¹ -
        B * (B + r • (1 : CMatrix a))⁻¹ =
      ∫ u in (0 : ℝ)..1,
        r • (audenaertPathResolvent A B u r * (A - B) *
          audenaertPathResolvent A B u r) := by
  let f : ℝ → CMatrix a := fun u =>
    audenaertPathMatrix A B u * (audenaertPathMatrix A B u + r • (1 : CMatrix a))⁻¹
  let fp : ℝ → CMatrix a := fun u =>
    r • (audenaertPathResolvent A B u r * (A - B) * audenaertPathResolvent A B u r)
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt f (fp u) u := by
    intro u hu
    have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le zero_le_one] using hu
    exact audenaertResolventPath_hasDerivAt hA hB huIcc.1 huIcc.2 hr
  have hcontV := audenaertPathResolvent_continuousOn hA hB hr
  have hint : IntervalIntegrable fp volume (0 : ℝ) 1 := by
    dsimp [fp]
    apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.const_smul
      ((hcontV.mul continuousOn_const).mul hcontV) r
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  symm
  calc
    ∫ u in (0 : ℝ)..1,
        r • (audenaertPathResolvent A B u r * (A - B) *
          audenaertPathResolvent A B u r)
        = ∫ u in (0 : ℝ)..1, fp u := rfl
    _ = f 1 - f 0 := hFTC
    _ = A * (A + r • (1 : CMatrix a))⁻¹ -
        B * (B + r • (1 : CMatrix a))⁻¹ := by
      simp [f, audenaertPathMatrix]

/-- Pointwise derivative-trace nonnegativity integrates to the endpoint resolvent difference. -/
public theorem audenaertResolventPath_trace_nonneg {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {r : ℝ} (hr : 0 < r) :
    0 ≤ (((positiveSpectralProjector (A - B)
        (hA.isHermitian.sub hB.isHermitian)) * B *
      (A * (A + r • (1 : CMatrix a))⁻¹ -
        B * (B + r • (1 : CMatrix a))⁻¹)).trace).re := by
  let H : CMatrix a := A - B
  let P := positiveSpectralProjector H (hA.isHermitian.sub hB.isHermitian)
  let fp : ℝ → CMatrix a := fun u =>
    r • (audenaertPathResolvent A B u r * H * audenaertPathResolvent A B u r)
  have hsub := audenaertResolventSub_eq_intervalIntegral hA hB hr
  have hfp : IntervalIntegrable fp volume (0 : ℝ) 1 := by
    simpa [fp, H] using audenaertResolventPath_derivative_intervalIntegrable hA hB hr
  have htrace := audenaertTraceLeftRight_intervalIntegral hfp P B
  rw [hsub]
  change 0 ≤ ((P * B * (∫ u in (0 : ℝ)..1, fp u)).trace).re
  rw [htrace]
  apply intervalIntegral.integral_nonneg zero_le_one
  intro u hu
  simpa [P, H, fp] using
    audenaertResolventPath_derivative_trace_nonneg hA hB hu.1 hu.2 hr

/-- Explicit bridge from the CFC integrand to Audenaert's resolvent form. -/
theorem audenaertRpowIntegrand_eq_resolvent {p r : ℝ} {A : CMatrix a}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hr : 0 < r) (hA : A.PosSemidef) :
    audenaertRpowIntegrand p r A = audenaertResolventIntegrand p r A := by
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  have hself : IsSelfAdjoint A := hA.isHermitian
  have hq_nonneg : quasispectrum ℝ A ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    exact NonnegSpectrumClass.quasispectrum_nonneg_of_nonneg A hA_nonneg x hx
  have hx_nonneg : ∀ x ∈ spectrum ℝ A, 0 ≤ x := by
    intro x hx
    exact hq_nonneg (spectrum_subset_quasispectrum ℝ A hx)
  have hden : ∀ x ∈ spectrum ℝ A, r + x ≠ 0 := by
    intro x hx hzero
    have hx0 := hx_nonneg x hx
    linarith
  have hfcont : ContinuousOn (Real.rpowIntegrand₀₁ p r) (quasispectrum ℝ A) := by
    exact (Real.continuousOn_rpowIntegrand₀₁_uncurry hp (quasispectrum ℝ A) hq_nonneg).uncurry_left r hr
  have halg : algebraMap ℝ (CMatrix a) r = r • (1 : CMatrix a) := by
    ext i j
    rw [Matrix.algebraMap_matrix_apply]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  dsimp [audenaertRpowIntegrand, audenaertResolventIntegrand]
  calc
    cfcₙ (Real.rpowIntegrand₀₁ p r) A = cfc (Real.rpowIntegrand₀₁ p r) A := by
      rw [cfcₙ_eq_cfc (a := A) (f := Real.rpowIntegrand₀₁ p r) (hf := hfcont)]
    _ = cfc (fun x : ℝ => r ^ (p - 1) * x / (r + x)) A := by
      apply cfc_congr
      intro x hx
      exact Real.rpowIntegrand₀₁_eq_pow_div hp (le_of_lt hr) (hx_nonneg x hx)
    _ = cfc (fun x : ℝ => (r ^ (p - 1) * x) / (r + x)) A := by
      congr with x
    _ = cfc (fun x : ℝ => r ^ (p - 1) * x) A *
        Ring.inverse (cfc (fun x : ℝ => r + x) A) := by
      rw [cfc_map_div (fun x : ℝ => r ^ (p - 1) * x)
        (fun x : ℝ => r + x) A hden (ha := hself)]
    _ = (r ^ (p - 1)) • A * Ring.inverse (algebraMap ℝ (CMatrix a) r + A) := by
      rw [cfc_const_mul_id (R := ℝ) (r := r ^ (p - 1)) (a := A) (ha := hself),
        cfc_const_add (R := ℝ) (r := r) (f := fun x : ℝ => x) (a := A) (ha := hself),
        cfc_id' ℝ A (ha := hself)]
    _ = (r ^ (p - 1)) • A * Ring.inverse (A + r • (1 : CMatrix a)) := by
      congr 2
      rw [halg, add_comm]
    _ = (r ^ (p - 1)) • A * (A + r • (1 : CMatrix a))⁻¹ := by
      rw [Matrix.nonsing_inv_eq_ringInverse]
    _ = r ^ (p - 1) • (A * (A + r • (1 : CMatrix a))⁻¹) := by
      rw [smul_mul_assoc]

/-- The CFC/resolvent integrand has the derivative-trace nonnegativity needed for Lemma 4. -/
public theorem audenaertRpowIntegrand_trace_nonneg {p r : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hr : 0 < r)
    {A B : CMatrix a} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (((positiveSpectralProjector (A - B)
        (hA.isHermitian.sub hB.isHermitian)) * B *
      (audenaertRpowIntegrand p r A -
       audenaertRpowIntegrand p r B)).trace).re := by
  let H : CMatrix a := A - B
  let P := positiveSpectralProjector H (hA.isHermitian.sub hB.isHermitian)
  have hbase :
      0 ≤ ((P * B *
        (A * (A + r • (1 : CMatrix a))⁻¹ -
          B * (B + r • (1 : CMatrix a))⁻¹)).trace).re := by
    simpa [P, H] using audenaertResolventPath_trace_nonneg hA hB hr
  have hscale : 0 ≤ r ^ (p - 1) :=
    (Real.rpow_pos_of_pos hr (p - 1)).le
  have hscaled :
      0 ≤ r ^ (p - 1) *
        ((P * B *
          (A * (A + r • (1 : CMatrix a))⁻¹ -
            B * (B + r • (1 : CMatrix a))⁻¹)).trace).re :=
    mul_nonneg hscale hbase
  rw [audenaertRpowIntegrand_eq_resolvent hp hr hA,
    audenaertRpowIntegrand_eq_resolvent hp hr hB]
  dsimp [audenaertResolventIntegrand]
  rw [← smul_sub]
  simpa [P, H, Matrix.trace_smul, mul_assoc] using hscaled

/-- Precise bridge from nonnegative real powers to real CFC powers. -/
theorem cMatrix_nnrpow_eq_rpow {p : ℝ≥0} (hp : 0 < p) (A : CMatrix a) :
    A ^ p = CFC.rpow A (p : ℝ) :=
  CFC.nnrpow_eq_rpow hp

/-- Endpoint `0` is separate from the open-interval integral representation. -/
theorem cMatrix_rpow_zero {A : CMatrix a} (hA : A.PosSemidef) :
    CFC.rpow A (0 : ℝ) = 1 :=
  CFC.rpow_zero A (ha := Matrix.nonneg_iff_posSemidef.mpr hA)

/-- Endpoint `1` is separate from the open-interval integral representation. -/
theorem cMatrix_rpow_one {A : CMatrix a} (hA : A.PosSemidef) :
    CFC.rpow A (1 : ℝ) = A :=
  CFC.rpow_one A (ha := Matrix.nonneg_iff_posSemidef.mpr hA)

/-- Existential fractional-power integral representation specialized to finite `CMatrix`.

The measure is chosen once from `p`; the two fields expose integrability and
the `CFC.rpow` equality for every PSD matrix.
-/
theorem audenaertRpowIntegralRepresentation {p : ℝ≥0}
    (hp : p ∈ Set.Ioo (0 : ℝ≥0) 1) :
    ∃ μ : Measure ℝ,
      (∀ ⦃A : CMatrix a⦄, A.PosSemidef →
        IntegrableOn (fun r : ℝ => audenaertRpowIntegrand (p : ℝ) r A) (Set.Ioi 0) μ) ∧
      (∀ ⦃A : CMatrix a⦄, A.PosSemidef →
        CFC.rpow A (p : ℝ) =
          ∫ r in Set.Ioi 0, audenaertRpowIntegrand (p : ℝ) r A ∂μ) := by
  obtain ⟨μ, hμ⟩ :=
    CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁
      (A := CMatrix a) (p := p) hp
  refine ⟨μ, ?_, ?_⟩
  · intro A hA
    exact (hμ A (Matrix.nonneg_iff_posSemidef.mpr hA)).1
  · intro A hA
    have hpow := (hμ A (Matrix.nonneg_iff_posSemidef.mpr hA)).2
    exact (CFC.nnrpow_eq_rpow hp.1 (a := A)).symm.trans hpow

/-- Same-measure difference form needed downstream by the Audenaert Lemma 4 route. -/
theorem audenaertRpowSubIntegralRepresentation {p : ℝ≥0}
    (hp : p ∈ Set.Ioo (0 : ℝ≥0) 1)
    {A B : CMatrix a} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ∃ μ : Measure ℝ,
      IntegrableOn (fun r : ℝ => audenaertRpowIntegrand (p : ℝ) r A) (Set.Ioi 0) μ ∧
      IntegrableOn (fun r : ℝ => audenaertRpowIntegrand (p : ℝ) r B) (Set.Ioi 0) μ ∧
      CFC.rpow A (p : ℝ) - CFC.rpow B (p : ℝ) =
        ∫ r in Set.Ioi 0,
          (audenaertRpowIntegrand (p : ℝ) r A -
            audenaertRpowIntegrand (p : ℝ) r B) ∂μ := by
  obtain ⟨μ, hint, hpow⟩ := audenaertRpowIntegralRepresentation (a := a) hp
  have hAint := hint hA
  have hBint := hint hB
  have hApow := hpow hA
  have hBpow := hpow hB
  refine ⟨μ, hAint, hBint, ?_⟩
  calc
    CFC.rpow A (p : ℝ) - CFC.rpow B (p : ℝ)
        = ∫ r in Set.Ioi 0, audenaertRpowIntegrand (p : ℝ) r A ∂μ -
            ∫ r in Set.Ioi 0, audenaertRpowIntegrand (p : ℝ) r B ∂μ := by
          rw [hApow, hBpow]
    _ = ∫ r in Set.Ioi 0,
          (audenaertRpowIntegrand (p : ℝ) r A -
            audenaertRpowIntegrand (p : ℝ) r B) ∂μ := by
          rw [integral_sub hAint hBint]

/-- Audenaert Lemma 4 on the open interval `0 < t < 1`. -/
public theorem audenaertLemma4_interior_trace_nonneg {t : ℝ≥0}
    (ht0 : 0 < t) (ht1 : t < 1)
    {A B : CMatrix a} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (((positiveSpectralProjector (A - B)
        (hA.isHermitian.sub hB.isHermitian)) * B *
      (CFC.rpow A (t : ℝ) - CFC.rpow B (t : ℝ))).trace).re := by
  let H : CMatrix a := A - B
  let P := positiveSpectralProjector H (hA.isHermitian.sub hB.isHermitian)
  let f : ℝ → CMatrix a := fun r =>
    audenaertRpowIntegrand (t : ℝ) r A - audenaertRpowIntegrand (t : ℝ) r B
  have htNN : t ∈ Set.Ioo (0 : ℝ≥0) 1 := ⟨ht0, ht1⟩
  have htReal : (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> exact_mod_cast ‹_›
  obtain ⟨μ, hAint, hBint, hpow⟩ :=
    audenaertRpowSubIntegralRepresentation (a := a) htNN hA hB
  have hf : IntegrableOn f (Set.Ioi 0) μ := by
    simpa [f] using hAint.sub hBint
  have htrace := audenaertTraceLeftRight_setIntegral hf P B
  rw [hpow]
  change 0 ≤ ((P * B * (∫ r in Set.Ioi 0, f r ∂μ)).trace).re
  rw [htrace]
  apply setIntegral_nonneg measurableSet_Ioi
  intro r hr
  simpa [P, H, f] using audenaertRpowIntegrand_trace_nonneg htReal hr hA hB

private theorem self_mul_positiveSpectralProjector_eq_posPart
    (H : CMatrix a) (hH : H.IsHermitian) :
    H * positiveSpectralProjector H hH = H⁺ := by
  have hsub : H⁺ - H⁻ = H := CFC.posPart_sub_negPart H hH.isSelfAdjoint
  calc
    H * positiveSpectralProjector H hH =
        (H⁺ - H⁻) * positiveSpectralProjector H hH := by
          rw [hsub]
    _ = H⁺ * positiveSpectralProjector H hH -
        H⁻ * positiveSpectralProjector H hH := by
          rw [sub_mul]
    _ = H⁺ := by
      rw [posPart_mul_positiveSpectralProjector, negPart_mul_positiveSpectralProjector]
      simp

/-- Audenaert Lemma 4 at endpoint `t = 0`. -/
public theorem audenaertLemma4_zero_trace_nonneg
    {A B : CMatrix a} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (((positiveSpectralProjector (A - B)
        (hA.isHermitian.sub hB.isHermitian)) * B *
      (CFC.rpow A (0 : ℝ) - CFC.rpow B (0 : ℝ))).trace).re := by
  rw [cMatrix_rpow_zero hA, cMatrix_rpow_zero hB]
  simp

/-- Audenaert Lemma 4 at endpoint `t = 1`. -/
public theorem audenaertLemma4_one_trace_nonneg
    {A B : CMatrix a} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (((positiveSpectralProjector (A - B)
        (hA.isHermitian.sub hB.isHermitian)) * B *
      (CFC.rpow A (1 : ℝ) - CFC.rpow B (1 : ℝ))).trace).re := by
  let H : CMatrix a := A - B
  let hH : H.IsHermitian := hA.isHermitian.sub hB.isHermitian
  let P := positiveSpectralProjector H hH
  have htrace :
      ((P * B * H).trace).re = ((H⁺ * B).trace).re := by
    have hHP := self_mul_positiveSpectralProjector_eq_posPart H hH
    calc
      ((P * B * H).trace).re = ((H * P * B).trace).re := by
        rw [Matrix.trace_mul_cycle]
      _ = ((H⁺ * B).trace).re := by
        rw [hHP]
  have hnonneg : 0 ≤ ((H⁺ * B).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg
      (Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg H)) hB
  rw [cMatrix_rpow_one hA, cMatrix_rpow_one hB]
  change 0 ≤ ((P * B * H).trace).re
  rwa [htrace]

/-- Audenaert Lemma 4 for all `0 ≤ t ≤ 1`, with endpoints handled separately. -/
public theorem audenaertLemma4_trace_nonneg {t : ℝ≥0} (ht : t ≤ 1)
    {A B : CMatrix a} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (((positiveSpectralProjector (A - B)
        (hA.isHermitian.sub hB.isHermitian)) * B *
      (CFC.rpow A (t : ℝ) - CFC.rpow B (t : ℝ))).trace).re := by
  by_cases ht_zero : t = 0
  · subst t
    simpa using audenaertLemma4_zero_trace_nonneg hA hB
  by_cases ht_one : t = 1
  · subst t
    simpa using audenaertLemma4_one_trace_nonneg hA hB
  have ht0 : 0 < t := lt_of_le_of_ne (show (0 : ℝ≥0) ≤ t from zero_le) (Ne.symm ht_zero)
  have ht1 : t < 1 := lt_of_le_of_ne ht ht_one
  exact audenaertLemma4_interior_trace_nonneg ht0 ht1 hA hB

/-- Difference of inverses for the PSD resolvents `A + r • 1` and `B + r • 1`. -/
theorem audenaertResolvent_inverse_sub {r : ℝ}
    {A B : CMatrix a} (hr : 0 < r) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (B + r • (1 : CMatrix a))⁻¹ - (A + r • (1 : CMatrix a))⁻¹ =
      (B + r • (1 : CMatrix a))⁻¹ * (A - B) *
        (A + r • (1 : CMatrix a))⁻¹ := by
  have hAu := audenaertResolvent_isUnit (a := a) hr hA
  have hBu := audenaertResolvent_isUnit (a := a) hr hB
  have hiff : IsUnit (B + r • (1 : CMatrix a)) ↔ IsUnit (A + r • (1 : CMatrix a)) :=
    ⟨fun _ => hAu, fun _ => hBu⟩
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (Matrix.inv_sub_inv
      (A := B + r • (1 : CMatrix a))
      (B := A + r • (1 : CMatrix a)) hiff)

/-- Resolvent multiplication written as `1 - r(A+rI)⁻¹`. -/
theorem audenaertResolvent_mul_eq_one_sub {r : ℝ}
    {A : CMatrix a} (hr : 0 < r) (hA : A.PosSemidef) :
    A * (A + r • (1 : CMatrix a))⁻¹ =
      1 - r • (A + r • (1 : CMatrix a))⁻¹ := by
  have hAu := audenaertResolvent_isUnit (a := a) hr hA
  have hright : (A + r • (1 : CMatrix a)) * (A + r • (1 : CMatrix a))⁻¹ = 1 := by
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hAu)
  calc
    A * (A + r • (1 : CMatrix a))⁻¹
        = ((A + r • (1 : CMatrix a)) - r • (1 : CMatrix a)) *
            (A + r • (1 : CMatrix a))⁻¹ := by
          rw [add_sub_cancel_right]
    _ = (A + r • (1 : CMatrix a)) * (A + r • (1 : CMatrix a))⁻¹ -
          (r • (1 : CMatrix a)) * (A + r • (1 : CMatrix a))⁻¹ := by
          rw [sub_mul]
    _ = 1 - r • (A + r • (1 : CMatrix a))⁻¹ := by
          rw [hright]
          simp

omit [Fintype a] in
private theorem one_sub_smul_sub_one_sub_smul (r : ℝ) (X Y : CMatrix a) :
    (1 : CMatrix a) - r • X - ((1 : CMatrix a) - r • Y) = r • (Y - X) := by
  simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Audenaert's resolvent difference identity, with `Δ = A - B`. -/
theorem audenaertResolventDifference {r : ℝ}
    {A B : CMatrix a} (hr : 0 < r) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A * (A + r • (1 : CMatrix a))⁻¹ -
        B * (B + r • (1 : CMatrix a))⁻¹ =
      r • ((B + r • (1 : CMatrix a))⁻¹ * (A - B) *
        (A + r • (1 : CMatrix a))⁻¹) := by
  rw [audenaertResolvent_mul_eq_one_sub hr hA,
    audenaertResolvent_mul_eq_one_sub hr hB]
  rw [one_sub_smul_sub_one_sub_smul]
  rw [audenaertResolvent_inverse_sub hr hA hB]

/-- The CFC integrand difference is the scalar resolvent-difference integrand. -/
theorem audenaertRpowIntegrand_sub_eq_resolventDifference {p r : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hr : 0 < r)
    {A B : CMatrix a} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    audenaertRpowIntegrand p r A - audenaertRpowIntegrand p r B =
      r ^ (p - 1) •
        (r • ((B + r • (1 : CMatrix a))⁻¹ * (A - B) *
          (A + r • (1 : CMatrix a))⁻¹)) := by
  rw [audenaertRpowIntegrand_eq_resolvent hp hr hA,
    audenaertRpowIntegrand_eq_resolvent hp hr hB]
  dsimp [audenaertResolventIntegrand]
  rw [← smul_sub]
  rw [audenaertResolventDifference hr hA hB]

/-- Audenaert's Theorem 1 on the left half `0 ≤ s ≤ 1/2`. -/
public theorem audenaertTraceInequality_leftHalf {s : ℝ}
    (hs0 : 0 ≤ s) (hsHalf : s ≤ 1 / 2)
    {A B : CMatrix a} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ((CFC.rpow A s * CFC.rpow B (1 - s)).trace).re ≥
      ((A + B - CFC.abs (A - B)).trace).re / 2 := by
  by_cases hsZero : s = 0
  · subst s
    rw [cMatrix_rpow_zero hA]
    rw [show (1 - 0 : ℝ) = 1 by norm_num, cMatrix_rpow_one hB, Matrix.one_mul]
    rw [audenaertTraceAbsRhs_eq_trace_sub_posPart hA hB]
    have hH : (A - B).IsHermitian := hA.isHermitian.sub hB.isHermitian
    have hmax :
        (((1 : CMatrix a) * (A - B)).trace).re ≤ ((A - B)⁺).trace.re :=
      trace_mul_le_trace_mul_posPart (1 : CMatrix a) (A - B)
        Matrix.PosSemidef.one le_rfl hH
    have htrace :
        (((1 : CMatrix a) * (A - B)).trace).re = A.trace.re - B.trace.re := by
      simp [Matrix.trace_sub]
    rw [htrace] at hmax
    linarith
  have hsPos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hsZero)
  let r : ℝ := 1 - s
  let t : ℝ := s / r
  have hparams : 0 < r ∧ 0 ≤ t ∧ t ≤ 1 ∧ r * t = s := by
    simpa [r, t] using audenaertLeftHalfParams hsPos hsHalf
  have hrPos : 0 < r := hparams.1
  have ht0 : 0 ≤ t := hparams.2.1
  have ht1 : t ≤ 1 := hparams.2.2.1
  have hrt : r * t = s := hparams.2.2.2
  have hrs : r + s = 1 := by
    dsimp [r]
    ring
  let X : CMatrix a := CFC.rpow A r
  let Y : CMatrix a := CFC.rpow B r
  have hX : X.PosSemidef := by simpa [X] using cMatrix_rpow_posSemidef (s := r) hA
  have hY : Y.PosSemidef := by simpa [Y] using cMatrix_rpow_posSemidef (s := r) hB
  have hXY : (X - Y).IsHermitian := hX.isHermitian.sub hY.isHermitian
  let P : CMatrix a := positiveSpectralProjector (X - Y) hXY
  let tNN : ℝ≥0 := ⟨t, ht0⟩
  have htNN : tNN ≤ 1 := by exact_mod_cast ht1
  have hXpow : CFC.rpow X (tNN : ℝ) = CFC.rpow A s := by
    simpa [X, tNN] using cMatrix_rpow_rpow_of_nonneg hA hrPos.le ht0 hrt
  have hYpow : CFC.rpow Y (tNN : ℝ) = CFC.rpow B s := by
    simpa [Y, tNN] using cMatrix_rpow_rpow_of_nonneg hB hrPos.le ht0 hrt
  have hXmul : X * CFC.rpow A s = A := by
    simpa [X] using cMatrix_rpow_mul_rpow_of_pos_add_eq_one hA hrPos hsPos hrs
  have hYmul : Y * CFC.rpow B s = B := by
    simpa [Y] using cMatrix_rpow_mul_rpow_of_pos_add_eq_one hB hrPos hsPos hrs
  have hlemma :
      0 ≤ ((P * Y * (CFC.rpow A s - CFC.rpow B s)).trace).re := by
    have h := audenaertLemma4_trace_nonneg (a := a) (t := tNN) htNN hX hY
    rw [hXpow, hYpow] at h
    have h' :
        0 ≤ ((positiveSpectralProjector (X - Y)
            (hX.isHermitian.sub hY.isHermitian) * Y *
          (CFC.rpow A s - CFC.rpow B s)).trace).re := h
    simpa [P, hXY] using h'
  have hPpart :
      ((P * B).trace).re ≤ ((P * Y * CFC.rpow A s).trace).re := by
    have htrace :
        ((P * Y * (CFC.rpow A s - CFC.rpow B s)).trace).re =
          ((P * Y * CFC.rpow A s).trace).re - ((P * B).trace).re := by
      have hYB : P * Y * CFC.rpow B s = P * B := by
        calc
          P * Y * CFC.rpow B s = P * (Y * CFC.rpow B s) := by
            rw [Matrix.mul_assoc]
          _ = P * B := by rw [hYmul]
      have hcomplex :
          (P * Y * (CFC.rpow A s - CFC.rpow B s)).trace =
            (P * Y * CFC.rpow A s).trace - (P * B).trace := by
        rw [Matrix.mul_sub, Matrix.trace_sub, hYB]
      simpa [Complex.sub_re] using congrArg Complex.re hcomplex
    linarith
  have hComp :
      (((1 - P) * Y * CFC.rpow A s).trace).re ≥
        (((1 - P) * A).trace).re := by
    simpa [P] using audenaertComplementProjector_trace_ge hs0 hA hX hY hXY hXmul
  have hdecomp :
      ((CFC.rpow A s * Y).trace).re =
        ((P * Y * CFC.rpow A s).trace).re +
          (((1 - P) * Y * CFC.rpow A s).trace).re := by
    have hcomplex :
        (CFC.rpow A s * Y).trace =
          (P * Y * CFC.rpow A s).trace +
            (((1 - P) * Y * CFC.rpow A s).trace) := by
      calc
        (CFC.rpow A s * Y).trace = (Y * CFC.rpow A s).trace := by
          rw [Matrix.trace_mul_comm]
        _ = (((P + (1 - P)) * (Y * CFC.rpow A s))).trace := by
          simp
        _ = (P * (Y * CFC.rpow A s) + (1 - P) * (Y * CFC.rpow A s)).trace := by
          rw [add_mul]
        _ = (P * Y * CFC.rpow A s).trace +
            (((1 - P) * Y * CFC.rpow A s).trace) := by
          simp [Matrix.trace_add, Matrix.mul_assoc]
    simpa [Complex.add_re] using congrArg Complex.re hcomplex
  have hblockLower :
      ((P * B).trace).re + (((1 - P) * A).trace).re ≤
        ((CFC.rpow A s * Y).trace).re := by
    rw [hdecomp]
    linarith
  have hbase :
      ((P * B).trace).re + (((1 - P) * A).trace).re =
        A.trace.re - ((P * (A - B)).trace).re := by
    simp [Matrix.trace_sub, Matrix.mul_sub, Matrix.sub_mul]
    ring
  have hPpos : P.PosSemidef := by
    simpa [P] using positiveSpectralProjector_posSemidef (X - Y) hXY
  have hPle : P ≤ 1 := by
    simpa [P] using positiveSpectralProjector_le_one (X - Y) hXY
  have hAB : (A - B).IsHermitian := hA.isHermitian.sub hB.isHermitian
  have hmax : ((P * (A - B)).trace).re ≤ ((A - B)⁺).trace.re :=
    trace_mul_le_trace_mul_posPart P (A - B) hPpos hPle hAB
  have htargetBase :
      A.trace.re - ((A - B)⁺).trace.re ≤
        ((P * B).trace).re + (((1 - P) * A).trace).re := by
    rw [hbase]
    linarith
  rw [audenaertTraceAbsRhs_eq_trace_sub_posPart hA hB]
  simpa [Y, r] using le_trans htargetBase hblockLower

/-- Audenaert's Theorem 1 on the right half `1/2 ≤ s ≤ 1`, by symmetry. -/
public theorem audenaertTraceInequality_rightHalf {s : ℝ}
    (hsHalf : 1 / 2 ≤ s) (hs1 : s ≤ 1)
    {A B : CMatrix a} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ((CFC.rpow A s * CFC.rpow B (1 - s)).trace).re ≥
      ((A + B - CFC.abs (A - B)).trace).re / 2 := by
  have hOneSub0 : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have hOneSubHalf : 1 - s ≤ 1 / 2 := by linarith
  have hleft :=
    audenaertTraceInequality_leftHalf (a := a) (s := 1 - s)
      hOneSub0 hOneSubHalf (A := B) (B := A) hB hA
  have hleft' :
      ((CFC.rpow B (1 - s) * CFC.rpow A s).trace).re ≥
        ((A + B - CFC.abs (A - B)).trace).re / 2 := by
    have hsimp : 1 - (1 - s) = s := by ring
    simpa [hsimp, add_comm, add_left_comm, add_assoc,
      audenaertTraceAbsRhs_swap A B] using hleft
  rw [audenaertTraceProduct_comm_re]
  exact hleft'

/-- Audenaert's finite-dimensional positive-operator trace inequality. -/
public theorem audenaertTraceInequality {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {A B : CMatrix a} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ((CFC.rpow A s * CFC.rpow B (1 - s)).trace).re ≥
      ((A + B - CFC.abs (A - B)).trace).re / 2 := by
  by_cases hsHalf : s ≤ 1 / 2
  · exact audenaertTraceInequality_leftHalf hs0 hsHalf hA hB
  · exact audenaertTraceInequality_rightHalf
      (le_of_lt (lt_of_not_ge hsHalf)) hs1 hA hB

namespace HypothesisTesting
namespace Audenaert

/-- Public catalog entrypoint for Audenaert's positive-operator trace inequality. -/
public theorem main {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {A B : CMatrix a} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ((CFC.rpow A s * CFC.rpow B (1 - s)).trace).re ≥
      ((A + B - CFC.abs (A - B)).trace).re / 2 :=
  audenaertTraceInequality hs0 hs1 hA hB

end Audenaert
end HypothesisTesting

end

end QIT
