/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Purification.ReferenceExtension
public import QIT.States.Purification.ReferenceIsometry
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Gram-factorization bridge

This module isolates the corrected matrix bridge needed by the purification
equivalence route registered from [Wilde2011Qst, qit-notes.tex:10320-10338]
and [Gour2024Resources, BookQRT.tex:2051-2069].

The abstract theorem factors maps with equal target-side Gram operators.  The
matrix theorem uses the `PureVector.amplitudeMatrix` convention from
`QIT.States.Purification.Gram`, where amplitudes are target rows and reference
columns, so the target Gram matrix is `A * Aᴴ`.
-/

@[expose] public section

namespace QIT

noncomputable section

namespace LinearMap

open Module

variable {E₁ E₂ F : Type*}
variable [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [FiniteDimensional ℂ E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂] [FiniteDimensional ℂ E₂]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Equal target-side Gram operators factor the second map through the adjoint
of a full-domain isometry. -/
theorem exists_comp_adjoint_eq_of_comp_adjoint_eq
    {T₁ : E₁ →ₗ[ℂ] F} {T₂ : E₂ →ₗ[ℂ] F}
    (hGram : T₁.comp T₁.adjoint = T₂.comp T₂.adjoint)
    (hfin : finrank ℂ E₁ ≤ finrank ℂ E₂) :
    ∃ U : E₁ →ₗᵢ[ℂ] E₂, T₂ = T₁.comp U.adjoint := by
  obtain ⟨U, hU⟩ :=
    exists_isometry_apply_adjoint_of_comp_adjoint_eq (T₁ := T₁) (T₂ := T₂) hGram hfin
  refine ⟨U, ?_⟩
  have hAdj : U.toLinearMap.comp T₁.adjoint = T₂.adjoint := by
    ext y
    exact hU y
  have h := congrArg LinearMap.adjoint hAdj
  simpa using h.symm

end LinearMap

namespace ReferenceIsometry

open Module

variable {a r₁ r₂ : Type*}
variable [Fintype a] [DecidableEq a]
variable [Fintype r₁] [DecidableEq r₁]
variable [Fintype r₂] [DecidableEq r₂]

/-- Equal target-row Gram matrices give a reference-side matrix isometry
factoring the second amplitude matrix through the first. -/
theorem exists_eq_mul_transpose_of_mul_conjTranspose_eq
    (A : Matrix a r₁ ℂ) (B : Matrix a r₂ ℂ)
    (hGram : A * Matrix.conjTranspose A = B * Matrix.conjTranspose B)
    (hcard : Fintype.card r₁ ≤ Fintype.card r₂) :
    ∃ V : ReferenceIsometry r₁ r₂, B = A * Matrix.transpose V.matrix := by
  classical
  let T₁ : EuclideanSpace ℂ r₁ →ₗ[ℂ] EuclideanSpace ℂ a := A.toEuclideanLin
  let T₂ : EuclideanSpace ℂ r₂ →ₗ[ℂ] EuclideanSpace ℂ a := B.toEuclideanLin
  have hGramLin : T₁.comp T₁.adjoint = T₂.comp T₂.adjoint := by
    dsimp [T₁, T₂]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint A,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint B]
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_mul] using
      congrArg Matrix.toEuclideanLin hGram
  have hfin :
      finrank ℂ (EuclideanSpace ℂ r₁) ≤ finrank ℂ (EuclideanSpace ℂ r₂) := by
    simpa [finrank_euclideanSpace] using hcard
  obtain ⟨U, hU⟩ :=
    LinearMap.exists_comp_adjoint_eq_of_comp_adjoint_eq (T₁ := T₁) (T₂ := T₂)
      hGramLin hfin
  let M : Matrix r₂ r₁ ℂ := Matrix.toEuclideanLin.symm U.toLinearMap
  have hMlin : M.toEuclideanLin = U.toLinearMap := by
    simp [M]
  have hMadj : Matrix.toEuclideanLin (Matrix.conjTranspose M) = U.adjoint := by
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hMlin]
  have hunitM : Matrix.conjTranspose M * M = 1 := by
    have hunitLin : (Matrix.conjTranspose M).toEuclideanLin.comp M.toEuclideanLin =
        (LinearMap.id : EuclideanSpace ℂ r₁ →ₗ[ℂ] EuclideanSpace ℂ r₁) := by
      simp [hMlin, hMadj]
    apply Matrix.toEuclideanLin.injective
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_mul, Matrix.toLpLin_one] using hunitLin
  let V : ReferenceIsometry r₁ r₂ :=
    { matrix := M.map star
      isometry := by
        ext i j
        have h := congrFun (congrFun hunitM j) i
        simpa [Matrix.mul_apply, Matrix.conjTranspose, Matrix.one_apply, Matrix.map_apply, eq_comm,
          Finset.mul_sum, mul_comm] using h }
  refine ⟨V, ?_⟩
  apply Matrix.toEuclideanLin.injective
  have htarget : B.toEuclideanLin = (A * Matrix.conjTranspose M).toEuclideanLin := by
    calc
      B.toEuclideanLin = A.toEuclideanLin.comp U.adjoint := by simpa [T₁, T₂] using hU
      _ = A.toEuclideanLin.comp (Matrix.conjTranspose M).toEuclideanLin := by rw [hMadj]
      _ = (A * Matrix.conjTranspose M).toEuclideanLin := by
        rw [Matrix.toLpLin_mul]
  simpa [V, Matrix.conjTranspose, Matrix.transpose] using htarget

end ReferenceIsometry

end

end QIT
