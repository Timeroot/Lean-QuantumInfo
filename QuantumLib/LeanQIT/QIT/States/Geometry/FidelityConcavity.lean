/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Purification.Uhlmann
import QIT.Classical.CQState

/-!
# Fidelity under convex combinations

This module proves the fixed-left quasiconcavity of finite-dimensional root
fidelity.  The proof uses a binary classical flag, the block-diagonal fidelity
formula, and monotonicity of fidelity under the partial trace.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

open Matrix

namespace QIT

universe u

noncomputable section

namespace State

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- A binary convex combination of normalized finite-dimensional states. -/
def convexCombination (t : ℝ) (ρ σ : State a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : State a where
  matrix := ((t : ℂ) • ρ.matrix) + (((1 - t : ℝ) : ℂ) • σ.matrix)
  pos := by
    exact Matrix.PosSemidef.add
      (ρ.pos.smul (by exact_mod_cast ht0))
      (σ.pos.smul (by exact_mod_cast sub_nonneg.mpr ht1))
  trace_eq_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      ρ.trace_eq_one, σ.trace_eq_one]
    simp

@[simp]
theorem convexCombination_matrix (t : ℝ) (ρ σ : State a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (convexCombination t ρ σ ht0 ht1).matrix =
      ((t : ℂ) • ρ.matrix) + (((1 - t : ℝ) : ℂ) • σ.matrix) :=
  rfl

@[simp]
theorem convexCombination_self (t : ℝ) (ρ : State a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    convexCombination t ρ ρ ht0 ht1 = ρ := by
  apply State.ext
  ext i j
  simp [convexCombination]
  ring

private theorem psdSqrt_real_smul_of_posSemidef
    {r : ℝ} (hr : 0 ≤ r) {M : CMatrix a} (hM : M.PosSemidef) :
    psdSqrt (((r : ℂ) • M)) =
      ((Real.sqrt r : ℝ) : ℂ) • psdSqrt M := by
  let S : CMatrix a := ((Real.sqrt r : ℝ) : ℂ) • psdSqrt M
  have hSsq : S * S = ((r : ℂ) • M) := by
    dsimp [S]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hr,
      psdSqrt_mul_self_of_posSemidef hM]
  have hSpos : S.PosSemidef := by
    have hscalar : (0 : ℂ) ≤ ((Real.sqrt r : ℝ) : ℂ) := by
      exact_mod_cast Real.sqrt_nonneg r
    exact Matrix.PosSemidef.smul (psdSqrt_pos M) hscalar
  change psdSqrt (((r : ℂ) • M)) = S
  simpa [psdSqrt, S] using
    (CFC.sqrt_unique (a := ((r : ℂ) • M)) (b := S) hSsq hSpos.nonneg)

private theorem traceNorm_psdSqrt_same_real_smul
    {r : ℝ} (hr : 0 ≤ r) {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    traceNorm
        (psdSqrt ((r : ℂ) • A) * psdSqrt ((r : ℂ) • B)) =
      r * traceNorm (psdSqrt A * psdSqrt B) := by
  rw [psdSqrt_real_smul_of_posSemidef hr hA,
    psdSqrt_real_smul_of_posSemidef hr hB,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hsqrt_sq : (Real.sqrt r) * Real.sqrt r = r := Real.mul_self_sqrt hr
  rw [show ((Real.sqrt r : ℂ) * (Real.sqrt r : ℂ)) = (r : ℂ) by exact_mod_cast hsqrt_sq]
  exact traceNorm_real_smul_eq hr _

private def binaryEnsemble
    (t : ℝ) (ρ σ : State a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ensemble Bool a where
  probs x := if x then ⟨t, ht0⟩ else ⟨1 - t, sub_nonneg.mpr ht1⟩
  weights_sum := by
    rw [Fintype.sum_bool]
    apply NNReal.eq
    change t + (1 - t) = 1
    ring
  states x := if x then ρ else σ

private theorem binaryEnsemble_averageState
    (t : ℝ) (ρ σ : State a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (binaryEnsemble t ρ σ ht0 ht1).averageState =
      convexCombination t ρ σ ht0 ht1 := by
  apply State.ext
  ext i j
  simp only [binaryEnsemble, Ensemble.averageState_matrix, Fintype.sum_bool,
    if_true, convexCombination_matrix, Matrix.add_apply, Matrix.smul_apply]
  change
    (t : ℂ) * ρ.matrix i j + ((1 - t : ℝ) : ℂ) * σ.matrix i j =
      (t : ℂ) * ρ.matrix i j + ((1 - t : ℝ) : ℂ) * σ.matrix i j
  rfl

private theorem binaryEnsemble_cqState_fidelity
    (t : ℝ) (ρ σ τ : State a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (binaryEnsemble t ρ ρ ht0 ht1).cqState.fidelity
        (binaryEnsemble t σ τ ht0 ht1).cqState =
      t * ρ.fidelity σ + (1 - t) * ρ.fidelity τ := by
  rw [State.fidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix]
  change
    traceNorm
        (psdSqrt (binaryEnsemble t ρ ρ ht0 ht1).cqState.matrix *
          psdSqrt (binaryEnsemble t σ τ ht0 ht1).cqState.matrix) =
      t * ρ.fidelity σ + (1 - t) * ρ.fidelity τ
  rw [Classical.cqState_eq_blockDiagonal, Classical.cqState_eq_blockDiagonal]
  rw [Classical.traceNorm_psdSqrt_blockDiagonal_mul_psdSqrt_blockDiagonal]
  · rw [Fintype.sum_bool]
    change
      traceNorm (psdSqrt ((t : ℂ) • ρ.matrix) * psdSqrt ((t : ℂ) • σ.matrix)) +
          traceNorm
            (psdSqrt (((1 - t : ℝ) : ℂ) • ρ.matrix) *
              psdSqrt (((1 - t : ℝ) : ℂ) • τ.matrix)) =
        t * ρ.fidelity σ + (1 - t) * ρ.fidelity τ
    rw [traceNorm_psdSqrt_same_real_smul ht0 ρ.pos σ.pos,
      traceNorm_psdSqrt_same_real_smul (sub_nonneg.mpr ht1) ρ.pos τ.pos]
    rfl
  · intro x
    have hp :
        (0 : ℂ) ≤ ((binaryEnsemble t ρ ρ ht0 ht1).probs x : ℂ) := by
      exact_mod_cast NNReal.coe_nonneg ((binaryEnsemble t ρ ρ ht0 ht1).probs x)
    exact ((binaryEnsemble t ρ ρ ht0 ht1).states x).pos.smul hp
  · intro x
    have hp :
        (0 : ℂ) ≤ ((binaryEnsemble t σ τ ht0 ht1).probs x : ℂ) := by
      exact_mod_cast NNReal.coe_nonneg ((binaryEnsemble t σ τ ht0 ht1).probs x)
    exact ((binaryEnsemble t σ τ ht0 ht1).states x).pos.smul hp

/-- For fixed left input, root fidelity is quasiconcave in the right state. -/
theorem fidelity_convexCombination_right_ge_min
    (ρ σ τ : State a) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    min (ρ.fidelity σ) (ρ.fidelity τ) ≤
      ρ.fidelity (convexCombination t σ τ ht0 ht1) := by
  let Eρ := binaryEnsemble t ρ ρ ht0 ht1
  let Eστ := binaryEnsemble t σ τ ht0 ht1
  have hmono := State.squaredFidelity_le_marginalB_squaredFidelity Eρ.cqState Eστ.cqState
  rw [State.squaredFidelity_eq_fidelity_sq,
    State.squaredFidelity_eq_fidelity_sq,
    Ensemble.cqState_marginalB_eq_averageState,
    Ensemble.cqState_marginalB_eq_averageState,
    binaryEnsemble_averageState,
    binaryEnsemble_averageState,
    convexCombination_self,
    binaryEnsemble_cqState_fidelity] at hmono
  have hright_nonneg :
      0 ≤ ρ.fidelity (convexCombination t σ τ ht0 ht1) :=
    State.fidelity_nonneg _ _
  have hweighted_min :
      min (ρ.fidelity σ) (ρ.fidelity τ) ≤
        t * ρ.fidelity σ + (1 - t) * ρ.fidelity τ := by
    have hminσ : min (ρ.fidelity σ) (ρ.fidelity τ) ≤ ρ.fidelity σ := min_le_left _ _
    have hminτ : min (ρ.fidelity σ) (ρ.fidelity τ) ≤ ρ.fidelity τ := min_le_right _ _
    nlinarith
  have hweighted_nonneg :
      0 ≤ t * ρ.fidelity σ + (1 - t) * ρ.fidelity τ := by
    exact add_nonneg
      (mul_nonneg ht0 (State.fidelity_nonneg _ _))
      (mul_nonneg (sub_nonneg.mpr ht1) (State.fidelity_nonneg _ _))
  have hweighted_le :
      t * ρ.fidelity σ + (1 - t) * ρ.fidelity τ ≤
        ρ.fidelity (convexCombination t σ τ ht0 ht1) := by
    nlinarith
  exact hweighted_min.trans hweighted_le

end State

end


end QIT
