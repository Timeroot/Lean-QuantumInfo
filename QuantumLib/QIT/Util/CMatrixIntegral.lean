/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Util.CMatrixCLM
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Bochner integration of complex matrices

`CMatrix ι` is a finite-dimensional normed space, so Bochner integration
commutes with every continuous linear map out of it.  Specialising the maps of
`QuantumLib.QIT.Util.CMatrixCLM` turns that single fact into the entrywise,
product, adjoint, trace, partial-trace and positivity rules used by the
unitary-twirl, decoupling, de Finetti, Frank--Lieb and Petz-kernel modules.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory

namespace QIT

universe u v

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {f : α → CMatrix ι}

/-- Bochner integration of a matrix-valued function is computed entrywise. -/
theorem cMatrix_integral_apply (hf : Integrable f μ) (i j : ι) :
    (∫ x, f x ∂μ) i j = ∫ x, f x i j ∂μ := by
  simpa [cMatrixEntryCLM] using
    ((cMatrixEntryCLM (ι := ι) i j).integral_comp_comm hf).symm

/-- Every entry of an integrable matrix-valued function is integrable. -/
theorem cMatrix_integrable_apply (hf : Integrable f μ) (i j : ι) :
    Integrable (fun x => f x i j) μ :=
  (cMatrixEntryCLM (ι := ι) i j).integrable_comp hf

/-- A constant left factor passes through a matrix Bochner integral. -/
theorem cMatrix_integral_mul_left (C : CMatrix ι) (hf : Integrable f μ) :
    ∫ x, C * f x ∂μ = C * ∫ x, f x ∂μ := by
  ext i j
  rw [cMatrix_integral_apply (hf.const_mul C)]
  simp only [Matrix.mul_apply]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl ?_
    intro k _
    rw [integral_const_mul, ← cMatrix_integral_apply hf k j]
  · intro k _
    exact (cMatrix_integrable_apply hf k j).const_mul _

/-- A constant right factor passes through a matrix Bochner integral. -/
theorem cMatrix_integral_mul_right (hf : Integrable f μ) (C : CMatrix ι) :
    ∫ x, f x * C ∂μ = (∫ x, f x ∂μ) * C := by
  ext i j
  rw [cMatrix_integral_apply (hf.mul_const C)]
  simp only [Matrix.mul_apply]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl ?_
    intro k _
    rw [integral_mul_const, ← cMatrix_integral_apply hf i k]
  · intro k _
    exact (cMatrix_integrable_apply hf i k).mul_const _

/-- The adjoint commutes with matrix Bochner integration. -/
theorem cMatrix_integral_conjTranspose (hf : Integrable f μ) :
    Matrix.conjTranspose (∫ x, f x ∂μ) = ∫ x, Matrix.conjTranspose (f x) ∂μ := by
  simpa [cMatrixConjTransposeCLM] using
    ((cMatrixConjTransposeCLM (ι := ι)).integral_comp_comm hf).symm

/-- The trace commutes with matrix Bochner integration. -/
theorem cMatrix_integral_trace (hf : Integrable f μ) :
    (∫ x, f x ∂μ).trace = ∫ x, (f x).trace ∂μ := by
  rw [Matrix.trace]
  change ∑ i, (∫ x, f x ∂μ) i i = ∫ x, ∑ i, f x i i ∂μ
  rw [MeasureTheory.integral_finsetSum]
  · exact Finset.sum_congr rfl fun i _ => cMatrix_integral_apply hf i i
  · intro i _
    exact cMatrix_integrable_apply hf i i

/-- Quadratic forms commute with matrix Bochner integration. -/
theorem cMatrix_integral_dotProduct_mulVec (hf : Integrable f μ) (x : ι → ℂ) :
    dotProduct (star x) (Matrix.mulVec (∫ t, f t ∂μ) x) =
      ∫ t, dotProduct (star x) (Matrix.mulVec (f t) x) ∂μ := by
  simp_rw [← cMatrixQuadraticCLM_apply x]
  exact ((cMatrixQuadraticCLM x).integral_comp_comm hf).symm

/-- The real-linear partial-trace map `X ↦ Tr_B X`. -/
def cMatrixTraceRightCLM {κ : Type v} [Fintype κ] [DecidableEq κ] :
    CMatrix (ι × κ) →L[ℝ] CMatrix ι :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun X => Matrix.traceRight X
       map_add' := by
        intro X Y
        exact Matrix.traceRight_add
       map_smul' := by
        intro c X
        exact Matrix.traceRight_smul c } :
      CMatrix (ι × κ) →ₗ[ℝ] CMatrix ι)

/-- The partial trace commutes with matrix Bochner integration. -/
theorem cMatrix_integral_traceRight {κ : Type v} [Fintype κ] [DecidableEq κ]
    {f : α → CMatrix (ι × κ)} (hf : Integrable f μ) :
    Matrix.traceRight (∫ x, f x ∂μ) = ∫ x, Matrix.traceRight (f x) ∂μ := by
  simpa [cMatrixTraceRightCLM] using
    ((cMatrixTraceRightCLM (ι := ι) (κ := κ)).integral_comp_comm hf).symm

/-- Bochner integration preserves positive semidefiniteness for matrix-valued
functions, up to almost-everywhere equality. -/
theorem cMatrix_integral_posSemidef_of_ae (hf : Integrable f μ)
    (hpos : ∀ᵐ t ∂μ, (f t).PosSemidef) :
    (∫ t, f t ∂μ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian, cMatrix_integral_conjTranspose hf]
    apply integral_congr_ae
    exact hpos.mono fun _ ht => ht.isHermitian.eq
  · intro x
    rw [cMatrix_integral_dotProduct_mulVec hf x]
    exact integral_nonneg_of_ae (hpos.mono fun _ ht => ht.dotProduct_mulVec_nonneg x)

/-- Monotonicity of Bochner set integration for matrix-valued functions in the
Loewner order.

Mathlib's scalar/order lemma needs a closed-order-topology instance which is not
available for `CMatrix`; this version proves the positive semidefinite
difference directly from quadratic forms. -/
theorem cMatrix_setIntegral_mono {s : Set α} (hs : MeasurableSet s)
    {f g : α → CMatrix ι} (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
    (hle : ∀ r ∈ s, f r ≤ g r) :
    ∫ r in s, f r ∂μ ≤ ∫ r in s, g r ∂μ := by
  have hdiffInt : IntegrableOn (fun r => g r - f r) s μ := hg.sub hf
  have hdiffPSD : (∫ r in s, (g r - f r) ∂μ).PosSemidef := by
    have hdiffInt' : Integrable (fun r => g r - f r) (μ.restrict s) := by
      simpa [IntegrableOn] using hdiffInt
    exact
      cMatrix_integral_posSemidef_of_ae (μ := μ.restrict s) hdiffInt'
        ((ae_restrict_iff' hs).mpr
          (ae_of_all μ fun r hr => Matrix.le_iff.mp (hle r hr)))
  have hsub :
      ∫ r in s, (g r - f r) ∂μ = (∫ r in s, g r ∂μ) - (∫ r in s, f r ∂μ) := by
    simpa [IntegrableOn] using
      integral_sub (μ := μ.restrict s)
        (by simpa [IntegrableOn] using hg)
        (by simpa [IntegrableOn] using hf)
  rw [hsub] at hdiffPSD
  exact Matrix.le_iff.mpr hdiffPSD

end

end QIT
