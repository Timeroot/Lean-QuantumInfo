/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.States.Purification.Uhlmann
public import QuantumLib.QIT.Classical.Ensemble
import QuantumLib.QIT.Classical.CQState

/-!
# Fidelity under convex combinations

This module proves the fixed-left quasiconcavity of finite-dimensional root
fidelity.  The proof uses a binary classical flag, the block-diagonal fidelity
formula, and monotonicity of fidelity under the partial trace.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

open Matrix hiding traceNorm

noncomputable section
universe u

open QIT

namespace MState

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- A binary convex combination of normalized finite-dimensional states. -/
def convexCombination (t : ℝ) (ρ σ : MState a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : MState a := .ofMatrix
  (matrix := ((t : ℂ) • ρ.m) + (((1 - t : ℝ) : ℂ) • σ.m))
  (pos := by
    exact Matrix.PosSemidef.add
      (ρ.psd.smul (by exact_mod_cast ht0))
      (σ.psd.smul (by exact_mod_cast sub_nonneg.mpr ht1)))
  (trace_eq_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      ρ.tr', σ.tr']
    simp)

@[simp]
theorem convexCombination_matrix (t : ℝ) (ρ σ : MState a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (convexCombination t ρ σ ht0 ht1).m =
      ((t : ℂ) • ρ.m) + (((1 - t : ℝ) : ℂ) • σ.m) :=
  MState.matrix_ofMatrix _ _ _

@[simp]
theorem convexCombination_self (t : ℝ) (ρ : MState a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    convexCombination t ρ ρ ht0 ht1 = ρ := by
  apply MState.ext
  ext i j
  simp [convexCombination]
  ring

private theorem traceNorm_psdSqrt_same_real_smul
    {r : ℝ} (hr : 0 ≤ r) {A B : CMatrix a}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    traceNorm
        (psdSqrt ((r : ℂ) • A) * psdSqrt ((r : ℂ) • B)) =
      r * traceNorm (psdSqrt A * psdSqrt B) := by
  rw [psdSqrt_real_smul hr hA,
    psdSqrt_real_smul hr hB,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hsqrt_sq : (Real.sqrt r) * Real.sqrt r = r := Real.mul_self_sqrt hr
  rw [show ((Real.sqrt r : ℂ) * (Real.sqrt r : ℂ)) = (r : ℂ) by exact_mod_cast hsqrt_sq]
  exact traceNorm_real_smul_eq hr _

/-- The two-point ensemble drawing `ρ` with probability `t` and `σ` with
probability `1 - t`. -/
def binaryEnsemble
    (t : ℝ) (ρ σ : MState a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    MEnsemble a Bool :=
  .ofProbs (fun x => if x then ⟨t, ht0⟩ else ⟨1 - t, sub_nonneg.mpr ht1⟩)
    (by
      rw [Fintype.sum_bool]
      apply NNReal.eq
      change t + (1 - t) = 1
      ring)
    (fun x => if x then ρ else σ)

/-- The probabilities of the two-point ensemble. -/
@[simp]
theorem binaryEnsemble_probs
    (t : ℝ) (ρ σ : MState a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Bool) :
    ((binaryEnsemble t ρ σ ht0 ht1).probs x : ℝ) = if x then t else 1 - t := by
  cases x <;> rfl

/-- The states of the two-point ensemble. -/
@[simp]
theorem binaryEnsemble_states
    (t : ℝ) (ρ σ : MState a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Bool) :
    (binaryEnsemble t ρ σ ht0 ht1).states x = if x then ρ else σ := rfl

/-- The average state of the two-point ensemble is the convex combination. -/
theorem binaryEnsemble_averageState
    (t : ℝ) (ρ σ : MState a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (binaryEnsemble t ρ σ ht0 ht1).averageState =
      convexCombination t ρ σ ht0 ht1 := by
  apply MState.ext
  ext i j
  simp only [binaryEnsemble, MEnsemble.averageState_matrix, Fintype.sum_bool,
    convexCombination_matrix, Matrix.add_apply, Matrix.smul_apply]
  change
    (t : ℂ) * ρ.m i j + ((1 - t : ℝ) : ℂ) * σ.m i j =
      (t : ℂ) * ρ.m i j + ((1 - t : ℝ) : ℂ) * σ.m i j
  rfl

private theorem binaryEnsemble_cqState_fidelity
    (t : ℝ) (ρ σ τ : MState a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (binaryEnsemble t ρ ρ ht0 ht1).cqState.fidelity
        (binaryEnsemble t σ τ ht0 ht1).cqState =
      t * ρ.fidelity σ + (1 - t) * ρ.fidelity τ := by
  rw [MState.fidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix]
  change
    traceNorm
        (psdSqrt (binaryEnsemble t ρ ρ ht0 ht1).cqState.m *
          psdSqrt (binaryEnsemble t σ τ ht0 ht1).cqState.m) =
      t * ρ.fidelity σ + (1 - t) * ρ.fidelity τ
  rw [Classical.cqState_eq_blockDiagonal, Classical.cqState_eq_blockDiagonal]
  rw [Classical.traceNorm_psdSqrt_blockDiagonal_mul_psdSqrt_blockDiagonal]
  · rw [Fintype.sum_bool]
    change
      traceNorm (psdSqrt ((t : ℂ) • ρ.m) * psdSqrt ((t : ℂ) • σ.m)) +
          traceNorm
            (psdSqrt (((1 - t : ℝ) : ℂ) • ρ.m) *
              psdSqrt (((1 - t : ℝ) : ℂ) • τ.m)) =
        t * ρ.fidelity σ + (1 - t) * ρ.fidelity τ
    rw [traceNorm_psdSqrt_same_real_smul ht0 ρ.psd σ.psd,
      traceNorm_psdSqrt_same_real_smul (sub_nonneg.mpr ht1) ρ.psd τ.psd]
    rfl
  · intro x
    have hp :
        (0 : ℂ) ≤ ((binaryEnsemble t ρ ρ ht0 ht1).probs x : ℂ) := by
      exact_mod_cast NNReal.coe_nonneg ((binaryEnsemble t ρ ρ ht0 ht1).probs x)
    exact ((binaryEnsemble t ρ ρ ht0 ht1).states x).psd.smul hp
  · intro x
    have hp :
        (0 : ℂ) ≤ ((binaryEnsemble t σ τ ht0 ht1).probs x : ℂ) := by
      exact_mod_cast NNReal.coe_nonneg ((binaryEnsemble t σ τ ht0 ht1).probs x)
    exact ((binaryEnsemble t σ τ ht0 ht1).states x).psd.smul hp

/-- For fixed left input, root fidelity is quasiconcave in the right state. -/
theorem fidelity_convexCombination_right_ge_min
    (ρ σ τ : MState a) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    min (ρ.fidelity σ) (ρ.fidelity τ) ≤
      ρ.fidelity (convexCombination t σ τ ht0 ht1) := by
  let Eρ := binaryEnsemble t ρ ρ ht0 ht1
  let Eστ := binaryEnsemble t σ τ ht0 ht1
  have hmono := MState.squaredFidelity_le_traceLeft_squaredFidelity Eρ.cqState Eστ.cqState
  rw [MState.squaredFidelity_eq_fidelity_sq,
    MState.squaredFidelity_eq_fidelity_sq,
    MEnsemble.cqState_traceLeft_eq_averageState,
    MEnsemble.cqState_traceLeft_eq_averageState,
    binaryEnsemble_averageState,
    binaryEnsemble_averageState,
    convexCombination_self,
    binaryEnsemble_cqState_fidelity] at hmono
  have hright_nonneg :
      0 ≤ ρ.fidelity (convexCombination t σ τ ht0 ht1) :=
    MState.fidelity_nonneg _ _
  have hweighted_min :
      min (ρ.fidelity σ) (ρ.fidelity τ) ≤
        t * ρ.fidelity σ + (1 - t) * ρ.fidelity τ := by
    have hminσ : min (ρ.fidelity σ) (ρ.fidelity τ) ≤ ρ.fidelity σ := min_le_left _ _
    have hminτ : min (ρ.fidelity σ) (ρ.fidelity τ) ≤ ρ.fidelity τ := min_le_right _ _
    nlinarith
  have hweighted_nonneg :
      0 ≤ t * ρ.fidelity σ + (1 - t) * ρ.fidelity τ := by
    exact add_nonneg
      (mul_nonneg ht0 (MState.fidelity_nonneg _ _))
      (mul_nonneg (sub_nonneg.mpr ht1) (MState.fidelity_nonneg _ _))
  have hweighted_le :
      t * ρ.fidelity σ + (1 - t) * ρ.fidelity τ ≤
        ρ.fidelity (convexCombination t σ τ ht0 ht1) := by
    nlinarith
  exact hweighted_min.trans hweighted_le

end MState
