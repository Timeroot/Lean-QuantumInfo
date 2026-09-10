/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.States.Schatten

/-!
# The maximally mixed state

The normalized maximally mixed state is `MState.uniform`. Its state-level matrix, marginals, and
square-root identities live here so that protocol and entropy modules can consume them without
reproving them.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open Matrix

noncomputable section
universe u v

open QIT

namespace MState

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

@[simp]
theorem uniform_matrix [Nonempty a] :
    (MState.uniform : MState a).m =
      (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) • (1 : CMatrix a) := by
  show (MState.ofClassical (ProbDistribution.uniform (α := a))).m = _
  rw [← DensityOp.mat_M, MState.coe_ofClassical, HermitianMat.diagonal_mat]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply, ProbDistribution.uniform_def, apply_ite,
    one_div]
  exact fun h h' => absurd h h'

/-- Tensoring a positive-definite state with a maximally mixed state preserves
positive definiteness. -/
theorem uniform_prod_posDef [Nonempty a]
    {σ : MState b} (hσ : σ.m.PosDef) :
    ((MState.uniform : MState a).prod σ).m.PosDef :=
  MState.PosDef.kron (MState.uniform_posDef (d := a)) hσ

omit [Fintype a] in theorem identityTensorStateMatrix_uniform [Nonempty b] :
    identityTensorStateMatrix (a := a) (MState.uniform : MState b) =
      ((((Fintype.card b : ℝ)⁻¹ : ℝ) : ℂ) • (1 : CMatrix (a × b))) := by
  ext x y
  by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;>
    simp [identityTensorStateMatrix, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff, h1, h2]

theorem uniform_traceRight [Nonempty a] [Nonempty b] :
    (MState.uniform : MState (a × b)).traceRight = (MState.uniform : MState a) := by
  apply MState.ext
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [Matrix.traceRight, Fintype.card_prod]
  · have hyx : ¬ y = x := fun h => hxy h.symm
    simp [Matrix.traceRight, Fintype.card_prod, hxy]

theorem uniform_traceLeft [Nonempty a] [Nonempty b] :
    (MState.uniform : MState (a × b)).traceLeft = (MState.uniform : MState b) := by
  apply MState.ext
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [Matrix.traceLeft, Fintype.card_prod]
    field_simp [show (Fintype.card a : ℂ) ≠ 0 by
      exact_mod_cast (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  · have hyx : ¬ y = x := fun h => hxy h.symm
    simp [Matrix.traceLeft, Fintype.card_prod, hxy]

/-- On a subsingleton finite system, every normalized state is maximally mixed. -/
theorem eq_uniform_of_subsingleton
    [Nonempty a] [Subsingleton a] (ρ : MState a) :
    ρ = (MState.uniform : MState a) := by
  apply MState.ext
  ext x y
  have hxy : x = y := Subsingleton.elim _ _
  subst y
  have hdiag : ρ.m x x = 1 := by
    have htrace := ρ.tr'
    rw [Matrix.trace] at htrace
    have hsum : (∑ z : a, ρ.m z z) = ρ.m x x := by
      apply Finset.sum_eq_single x
      · intro z _ hz
        exact False.elim (hz (Subsingleton.elim z x))
      · intro h
        exact False.elim (h (Finset.mem_univ x))
    have hsum_diag :
        (∑ z : a, Matrix.diag ρ.m z) = ρ.m x x := by
      simpa [Matrix.diag] using hsum
    rw [hsum_diag] at htrace
    exact htrace
  have hcard : (Fintype.card a : ℝ) = 1 := by
    exact_mod_cast
      (Fintype.card_eq_one_iff.mpr ⟨x, fun y => Subsingleton.elim y x⟩)
  simp [hdiag, hcard]

theorem uniform_sqrtMatrix [Nonempty a] :
    (MState.uniform : MState a).sqrtMatrix =
      (((Real.sqrt ((Fintype.card a : ℝ)⁻¹) : ℝ) : ℂ) •
        (1 : CMatrix a)) := by
  rw [MState.sqrtMatrix, uniform_matrix]
  exact psdSqrt_real_smul_one (a := a)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem uniform_prod_sqrtMatrix [Nonempty a] (σ : MState b) :
    ((MState.uniform : MState a).prod σ).sqrtMatrix =
      ((Real.sqrt ((Fintype.card a : ℝ)⁻¹) : ℝ) : ℂ) •
        ((1 : CMatrix a) ⊗ₖ σ.sqrtMatrix) := by
  rw [MState.sqrtMatrix, MState.prod_m]
  rw [psdSqrt_kronecker (MState.uniform : MState a).psd σ.psd]
  change ((MState.uniform : MState a).sqrtMatrix) ⊗ₖ (σ.sqrtMatrix) =
    ((Real.sqrt ((Fintype.card a : ℝ)⁻¹) : ℝ) : ℂ) •
      (1 : CMatrix a) ⊗ₖ σ.sqrtMatrix
  rw [uniform_sqrtMatrix (a := a)]
  ext x y
  simp [Matrix.kroneckerMap_apply, mul_assoc]

theorem sqrt_identityTensorStateMatrix_eq_sqrt_card_smul_uniform_prod_sqrtMatrix
    [Nonempty a] (σ : MState b) :
    (1 : CMatrix a) ⊗ₖ σ.sqrtMatrix =
      ((Real.sqrt (Fintype.card a : ℝ) : ℂ) •
        ((MState.uniform : MState a).prod σ).sqrtMatrix) := by
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hreal :
      Real.sqrt (Fintype.card a : ℝ) *
          Real.sqrt ((Fintype.card a : ℝ)⁻¹) = 1 := by
    rw [← Real.sqrt_mul (le_of_lt hcard_pos)]
    rw [mul_inv_cancel₀ hcard_pos.ne', Real.sqrt_one]
  rw [uniform_prod_sqrtMatrix (a := a) σ]
  ext x y
  simp [Matrix.kroneckerMap_apply]

theorem identityTensorStateMatrix_eq_card_smul_uniform_prod
    [Nonempty a] (σ : MState b) :
    identityTensorStateMatrix (a := a) σ =
      ((Fintype.card a : ℂ) • ((MState.uniform : MState a).prod σ).m) := by
  have hcard_ne : (Fintype.card a : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  ext x y
  simp [identityTensorStateMatrix, uniform_matrix, hcard_ne,
    Matrix.kroneckerMap_apply, mul_assoc]

end MState
