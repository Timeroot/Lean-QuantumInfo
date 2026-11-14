/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Schatten

/-!
# Canonical maximally mixed states

The normalized maximally mixed state and its state-level matrix, positivity,
marginal, and square-root identities live here so that protocol and entropy
modules can consume them without owning the construction.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace QIT

universe u v

noncomputable section

namespace State

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The normalized maximally mixed state on a nonempty finite system. -/
def maximallyMixed (a : Type u) [Fintype a] [DecidableEq a] [Nonempty a] : State a where
  matrix := (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) • (1 : CMatrix a)
  pos := by
    have hscalar : (0 : ℂ) ≤ (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) := by
      exact_mod_cast inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card a : ℕ))
    exact Matrix.PosSemidef.smul Matrix.PosSemidef.one hscalar
  trace_eq_one := by
    rw [Matrix.trace_smul, Matrix.trace_one]
    have hcard : (Fintype.card a : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    norm_num [hcard]

@[simp]
theorem maximallyMixed_matrix [Nonempty a] :
    (maximallyMixed a).matrix =
      (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) • (1 : CMatrix a) :=
  rfl

/-- The canonical maximally mixed state is positive definite on a nonempty
finite system. -/
theorem maximallyMixed_posDef [Nonempty a] :
    (maximallyMixed a).matrix.PosDef := by
  rw [maximallyMixed_matrix]
  have hcard_pos : 0 < ((Fintype.card a : ℝ)⁻¹) := by
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos_iff.mpr inferInstance)
  have hcardC_pos : (0 : ℂ) < (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) := by
    exact_mod_cast hcard_pos
  simpa using
    (Matrix.PosDef.smul (Matrix.PosDef.one : (1 : CMatrix a).PosDef) hcardC_pos)

/-- Tensoring a positive-definite state with a maximally mixed state preserves
positive definiteness. -/
theorem maximallyMixed_prod_posDef [Nonempty a]
    {σ : State b} (hσ : σ.matrix.PosDef) :
    ((maximallyMixed a).prod σ).matrix.PosDef :=
  State.prod_posDef (maximallyMixed_posDef (a := a)) hσ

omit [Fintype a] in theorem identityTensorStateMatrix_maximallyMixed [Nonempty b] :
    identityTensorStateMatrix (a := a) (maximallyMixed b) =
      ((((Fintype.card b : ℝ)⁻¹ : ℝ) : ℂ) • (1 : CMatrix (Prod a b))) := by
  ext x y
  by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;>
    simp [identityTensorStateMatrix, maximallyMixed, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff, h1, h2]

theorem maximallyMixed_marginalA [Nonempty a] [Nonempty b] :
    (maximallyMixed (Prod a b)).marginalA = maximallyMixed a := by
  apply State.ext
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [State.marginalA, partialTraceB, maximallyMixed,
      Fintype.card_prod]
  · have hyx : ¬ y = x := fun h => hxy h.symm
    simp [State.marginalA, partialTraceB, maximallyMixed,
      Fintype.card_prod, hxy]

theorem maximallyMixed_marginalB [Nonempty a] [Nonempty b] :
    (maximallyMixed (Prod a b)).marginalB = maximallyMixed b := by
  apply State.ext
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [State.marginalB, partialTraceA, maximallyMixed,
      Fintype.card_prod]
    field_simp [show (Fintype.card a : ℂ) ≠ 0 by
      exact_mod_cast (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  · have hyx : ¬ y = x := fun h => hxy h.symm
    simp [State.marginalB, partialTraceA, maximallyMixed,
      Fintype.card_prod, hxy]

/-- On a subsingleton finite system, every normalized state is maximally mixed. -/
theorem eq_maximallyMixed_of_subsingleton
    [Nonempty a] [Subsingleton a] (ρ : State a) :
    ρ = maximallyMixed a := by
  apply State.ext
  ext x y
  have hxy : x = y := Subsingleton.elim _ _
  subst y
  have hdiag : ρ.matrix x x = 1 := by
    have htrace := ρ.trace_eq_one
    rw [Matrix.trace] at htrace
    have hsum : (∑ z : a, ρ.matrix z z) = ρ.matrix x x := by
      apply Finset.sum_eq_single x
      · intro z _ hz
        exact False.elim (hz (Subsingleton.elim z x))
      · intro h
        exact False.elim (h (Finset.mem_univ x))
    have hsum_diag :
        (∑ z : a, Matrix.diag ρ.matrix z) = ρ.matrix x x := by
      simpa [Matrix.diag] using hsum
    rw [hsum_diag] at htrace
    exact htrace
  have hcard : (Fintype.card a : ℝ) = 1 := by
    exact_mod_cast
      (Fintype.card_eq_one_iff.mpr ⟨x, fun y => Subsingleton.elim y x⟩)
  simp [maximallyMixed, hdiag, hcard]

private theorem psdSqrt_kronecker_state {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {A : CMatrix a} {B : CMatrix b}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    psdSqrt (Matrix.kronecker A B) =
      Matrix.kronecker (psdSqrt A) (psdSqrt B) := by
  simp only [psdSqrt, CFC.sqrt_eq_rpow]
  exact cMatrix_rpow_kronecker_nonneg hA hB (by norm_num : (0 : ℝ) ≤ 1 / 2)

theorem maximallyMixed_sqrtMatrix [Nonempty a] :
    (maximallyMixed a).sqrtMatrix =
      (((Real.sqrt ((Fintype.card a : ℝ)⁻¹) : ℝ) : ℂ) •
        (1 : CMatrix a)) := by
  rw [State.sqrtMatrix, maximallyMixed_matrix]
  exact psdSqrt_real_smul_one (a := a)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem maximallyMixed_prod_sqrtMatrix [Nonempty a] (σ : State b) :
    ((maximallyMixed a).prod σ).sqrtMatrix =
      ((Real.sqrt ((Fintype.card a : ℝ)⁻¹) : ℝ) : ℂ) •
        Matrix.kronecker (1 : CMatrix a) σ.sqrtMatrix := by
  rw [State.sqrtMatrix, State.prod]
  rw [psdSqrt_kronecker_state (maximallyMixed a).pos σ.pos]
  change Matrix.kronecker ((maximallyMixed a).sqrtMatrix) (σ.sqrtMatrix) =
    ((Real.sqrt ((Fintype.card a : ℝ)⁻¹) : ℝ) : ℂ) •
      Matrix.kronecker (1 : CMatrix a) σ.sqrtMatrix
  rw [maximallyMixed_sqrtMatrix (a := a)]
  ext x y
  simp [Matrix.kroneckerMap_apply, mul_assoc]

theorem sqrt_identityTensorStateMatrix_eq_sqrt_card_smul_maximallyMixed_prod_sqrtMatrix
    [Nonempty a] (σ : State b) :
    Matrix.kronecker (1 : CMatrix a) σ.sqrtMatrix =
      ((Real.sqrt (Fintype.card a : ℝ) : ℂ) •
        ((maximallyMixed a).prod σ).sqrtMatrix) := by
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hreal :
      Real.sqrt (Fintype.card a : ℝ) *
          Real.sqrt ((Fintype.card a : ℝ)⁻¹) = 1 := by
    rw [← Real.sqrt_mul (le_of_lt hcard_pos)]
    rw [mul_inv_cancel₀ hcard_pos.ne', Real.sqrt_one]
  rw [maximallyMixed_prod_sqrtMatrix (a := a) σ]
  ext x y
  simp [Matrix.kroneckerMap_apply]

theorem identityTensorStateMatrix_eq_card_smul_maximallyMixed_prod
    [Nonempty a] (σ : State b) :
    identityTensorStateMatrix (a := a) σ =
      ((Fintype.card a : ℂ) • ((maximallyMixed a).prod σ).matrix) := by
  have hcard_ne : (Fintype.card a : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  ext x y
  simp [identityTensorStateMatrix, State.prod, maximallyMixed_matrix, hcard_ne,
    Matrix.kroneckerMap_apply, mul_assoc]

end State

end
end QIT
