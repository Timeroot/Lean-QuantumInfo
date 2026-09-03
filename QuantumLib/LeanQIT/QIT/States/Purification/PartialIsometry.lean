/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Purification.GramFacts

/-!
# Partial isometry between adjoint ranges

This module isolates the second finite-dimensional linear-algebra step needed
by the purification-equivalence route registered from [Wilde2011Qst,
qit-notes.tex:10320-10338] and [Gour2024Resources,
BookQRT.tex:2051-2069].

Given equal target-side Gram operators `T.comp T.adjoint`, the adjoint ranges
are identified by the rule `T₁.adjoint y ↦ T₂.adjoint y`.  The equal-kernel
fact from `QIT.States.Purification.GramFacts` makes the rule well-defined, and the equal
adjoint-image inner-product fact makes it a `LinearIsometry`.
-/

@[expose] public section

namespace QIT

noncomputable section

namespace LinearMap

variable {E₁ E₂ F : Type*}
variable [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [FiniteDimensional ℂ E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂] [FiniteDimensional ℂ E₂]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- The underlying linear map on adjoint ranges used to bundle
`adjointRangeIsometry`. -/
def adjointRangeMap
    {T₁ : E₁ →ₗ[ℂ] F} {T₂ : E₂ →ₗ[ℂ] F}
    (hGram : T₁.comp T₁.adjoint = T₂.comp T₂.adjoint) :
    LinearMap.range T₁.adjoint →ₗ[ℂ] LinearMap.range T₂.adjoint where
  toFun x := ⟨T₂.adjoint (Classical.choose x.property),
    LinearMap.mem_range_self T₂.adjoint (Classical.choose x.property)⟩
  map_add' x y := by
    apply Subtype.ext
    let sx : F := Classical.choose x.property
    let sy : F := Classical.choose y.property
    let sxy : F := Classical.choose (x + y).property
    have hsx : T₁.adjoint sx = x := Classical.choose_spec x.property
    have hsy : T₁.adjoint sy = y := Classical.choose_spec y.property
    have hsxy : T₁.adjoint sxy = x + y := Classical.choose_spec (x + y).property
    have hker : sxy - (sx + sy) ∈ LinearMap.ker T₁.adjoint := by
      rw [LinearMap.mem_ker]
      calc
        T₁.adjoint (sxy - (sx + sy)) =
            T₁.adjoint sxy - (T₁.adjoint sx + T₁.adjoint sy) := by simp
        _ = ↑(x + y) - (↑x + ↑y) := by
          rw [hsxy, hsx, hsy]
          rw [show ((x + y : LinearMap.range T₁.adjoint) : E₁) = (x : E₁) + y by rfl]
        _ = 0 := by simp
    have hker₂ : sxy - (sx + sy) ∈ LinearMap.ker T₂.adjoint := by
      rwa [ker_adjoint_eq_of_comp_adjoint_eq hGram] at hker
    have hzero : T₂.adjoint (sxy - (sx + sy)) = 0 := LinearMap.mem_ker.mp hker₂
    have hdiff : T₂.adjoint sxy - (T₂.adjoint sx + T₂.adjoint sy) = 0 := by
      simpa using hzero
    change T₂.adjoint sxy = T₂.adjoint sx + T₂.adjoint sy
    exact sub_eq_zero.mp hdiff
  map_smul' c x := by
    apply Subtype.ext
    let sx : F := Classical.choose x.property
    let scx : F := Classical.choose (c • x).property
    have hsx : T₁.adjoint sx = x := Classical.choose_spec x.property
    have hscx : T₁.adjoint scx = c • x := Classical.choose_spec (c • x).property
    have hker : scx - c • sx ∈ LinearMap.ker T₁.adjoint := by
      rw [LinearMap.mem_ker]
      calc
        T₁.adjoint (scx - c • sx) = T₁.adjoint scx - c • T₁.adjoint sx := by simp
        _ = ↑(c • x) - c • ↑x := by
          rw [hscx, hsx]
          rw [show ((c • x : LinearMap.range T₁.adjoint) : E₁) = c • (x : E₁) by rfl]
        _ = 0 := by simp
    have hker₂ : scx - c • sx ∈ LinearMap.ker T₂.adjoint := by
      rwa [ker_adjoint_eq_of_comp_adjoint_eq hGram] at hker
    have hzero : T₂.adjoint (scx - c • sx) = 0 := LinearMap.mem_ker.mp hker₂
    have hdiff : T₂.adjoint scx - c • T₂.adjoint sx = 0 := by
      simpa using hzero
    change T₂.adjoint scx = c • T₂.adjoint sx
    exact sub_eq_zero.mp hdiff

/-- Equal target-side Gram operators identify the adjoint ranges by a linear
isometry sending `T₁.adjoint y` to `T₂.adjoint y`. -/
def adjointRangeIsometry
    {T₁ : E₁ →ₗ[ℂ] F} {T₂ : E₂ →ₗ[ℂ] F}
    (hGram : T₁.comp T₁.adjoint = T₂.comp T₂.adjoint) :
    LinearMap.range T₁.adjoint →ₗᵢ[ℂ] LinearMap.range T₂.adjoint :=
  (adjointRangeMap hGram).isometryOfInner <| by
    intro x y
    let sx : F := Classical.choose x.property
    let sy : F := Classical.choose y.property
    have hsx : T₁.adjoint sx = x := Classical.choose_spec x.property
    have hsy : T₁.adjoint sy = y := Classical.choose_spec y.property
    calc
      inner ℂ (adjointRangeMap hGram x) (adjointRangeMap hGram y) =
          inner ℂ (T₂.adjoint sx) (T₂.adjoint sy) := by
        change inner ℂ (T₂.adjoint (Classical.choose x.property))
          (T₂.adjoint (Classical.choose y.property)) =
            inner ℂ (T₂.adjoint sx) (T₂.adjoint sy)
        rfl
      _ = inner ℂ (T₁.adjoint sx) (T₁.adjoint sy) :=
          (adjoint_inner_adjoint_of_comp_adjoint_eq hGram sx sy).symm
      _ = inner ℂ x y := by rw [hsx, hsy, Submodule.coe_inner]

/-- The adjoint-range isometry applies to a canonical adjoint representative
by replacing `T₁.adjoint` with `T₂.adjoint`. -/
theorem adjointRangeIsometry_apply_adjoint
    {T₁ : E₁ →ₗ[ℂ] F} {T₂ : E₂ →ₗ[ℂ] F}
    (hGram : T₁.comp T₁.adjoint = T₂.comp T₂.adjoint) (y : F) :
    adjointRangeIsometry hGram ⟨T₁.adjoint y, LinearMap.mem_range_self T₁.adjoint y⟩ =
      ⟨T₂.adjoint y, LinearMap.mem_range_self T₂.adjoint y⟩ := by
  apply Subtype.ext
  let sy : F := Classical.choose (LinearMap.mem_range_self T₁.adjoint y)
  have hsy : T₁.adjoint sy = T₁.adjoint y :=
    Classical.choose_spec (LinearMap.mem_range_self T₁.adjoint y)
  have hker : sy - y ∈ LinearMap.ker T₁.adjoint := by
    rw [LinearMap.mem_ker]
    simp [hsy]
  have hker₂ : sy - y ∈ LinearMap.ker T₂.adjoint := by
    rwa [ker_adjoint_eq_of_comp_adjoint_eq hGram] at hker
  have hzero : T₂.adjoint (sy - y) = 0 := LinearMap.mem_ker.mp hker₂
  have hdiff : T₂.adjoint sy - T₂.adjoint y = 0 := by
    simpa using hzero
  change ↑(adjointRangeIsometry hGram ⟨T₁.adjoint y, LinearMap.mem_range_self T₁.adjoint y⟩) =
    T₂.adjoint y
  simp only [adjointRangeIsometry, LinearMap.coe_isometryOfInner, adjointRangeMap]
  change T₂.adjoint sy = T₂.adjoint y
  exact sub_eq_zero.mp hdiff

end LinearMap

end

end QIT
