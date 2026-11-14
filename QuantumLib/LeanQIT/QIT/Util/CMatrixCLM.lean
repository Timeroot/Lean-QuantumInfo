/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.Matrix
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Continuous linear maps on complex matrices

The canonical real- and complex-linear continuous maps on `CMatrix ι` that
recur across the analysis layers: entry extraction, conjugate transpose, and
the quadratic form `A ↦ x† A x`.  Consolidating them here removes the private
duplicates that previously lived in the unitary-twirl, Frank–Lieb scalar
operator, cq-guessing, and Petz-kernel modules.
-/

@[expose] public section

open scoped ComplexOrder
open Matrix

namespace QIT

universe u

noncomputable section

/-- The real-linear entry-extraction map `A ↦ A i j`. -/
noncomputable def cMatrixEntryCLM {ι : Type u} [Fintype ι] [DecidableEq ι]
    (i j : ι) : CMatrix ι →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun A => A i j
       map_add' := by
        intro A B
        rfl
       map_smul' := by
        intro c A
        simp [Matrix.smul_apply] } :
      CMatrix ι →ₗ[ℝ] ℂ)

/-- The complex-linear entry-extraction map `A ↦ A i j`. -/
noncomputable def cMatrixEntryCLM_complex {ι : Type u} [Fintype ι] [DecidableEq ι]
    (i j : ι) : CMatrix ι →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun A => A i j
       map_add' := by
        intro A B
        rfl
       map_smul' := by
        intro c A
        simp [Matrix.smul_apply] } :
      CMatrix ι →ₗ[ℂ] ℂ)

/-- The real-linear conjugate-transpose map `A ↦ A†`. -/
noncomputable def cMatrixConjTransposeCLM {ι : Type u} [Fintype ι] [DecidableEq ι] :
    CMatrix ι →L[ℝ] CMatrix ι :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun A => A.conjTranspose
       map_add' := by
        intro A B
        rw [Matrix.conjTranspose_add]
       map_smul' := by
        intro c A
        rw [Matrix.conjTranspose_smul]
        simp } :
      CMatrix ι →ₗ[ℝ] CMatrix ι)

/-- The complex-linear quadratic form `A ↦ x† A x`. -/
noncomputable def cMatrixQuadraticCLM {ι : Type u} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) : CMatrix ι →L[ℂ] ℂ :=
  ∑ i, ∑ j, (star (x i) * x j) • cMatrixEntryCLM_complex (ι := ι) i j

/-- The quadratic-form CLM unfolds to the dot-product expression `x† (Ax)`. -/
theorem cMatrixQuadraticCLM_apply {ι : Type u} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (A : CMatrix ι) :
    cMatrixQuadraticCLM x A = dotProduct (star x) (Matrix.mulVec A x) := by
  simp [cMatrixQuadraticCLM, cMatrixEntryCLM_complex, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

end

end QIT
