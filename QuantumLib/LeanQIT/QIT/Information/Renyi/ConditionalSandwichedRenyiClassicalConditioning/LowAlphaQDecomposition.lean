/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

import Mathlib.Algebra.Order.CompleteField
public import QIT.Information.Renyi.ConditionalRenyiClassical
public import QIT.Information.Renyi.SandwichedRenyiOptimizedUSC
public import QIT.Information.Renyi.ConditionalSandwichedRenyiDuality
public import QIT.Information.Renyi.ConditionalSandwichedRenyiAdditivity
public import QIT.Measurements.Projective
public import QIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.BlockAlgebra

/-!
# low-alpha Q decomposition

Responsibility layer of the sandwiched conditional Renyi classical-conditioning
source route.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Pointwise
open Matrix

namespace QIT

universe u v w

noncomputable section

variable {A : Type u} {B : Type v} {Y : Type w}
variable [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
variable [Fintype Y] [DecidableEq Y]

namespace State

/-! ### Ensemble specialization and support sum -/

theorem sandwichedRenyiQ_cq_reference_decomposition
    (E : Ensemble Y (A × B)) (F : Ensemble Y B) {α : ℝ}
    (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyiQ
        (State.cqConditioningState E).matrix
        (identityTensorStateMatrix (a := A)
          (F.cqState.reindex (Equiv.prodComm Y B)))
        (State.cqConditioningState E).pos
        (identityTensorStateMatrix_posSemidef_of_state (a := A)
          (F.cqState.reindex (Equiv.prodComm Y B))) α =
      ∑ y, (E.probs y : ℝ) ^ α * (F.probs y : ℝ) ^ (1 - α) *
        sandwichedRenyiQ (E.states y).matrix
          (identityTensorStateMatrix (a := A) (F.states y))
          (E.states y).pos
          (identityTensorStateMatrix_posSemidef_of_state (a := A)
            (F.states y)) α := by
  have hdecomp := sandwichedRenyiQ_fixedReference_blockDiagonal
      (fun y => conditionalRenyiBlock E y)
      (fun y => (F.probs y : ℂ) •
        identityTensorStateMatrix (a := A) (F.states y))
      (fun y => conditionalRenyiBlock_posSemidef E y)
      (fun y => (identityTensorStateMatrix_posSemidef_of_state
        (a := A) (F.states y)).smul (by
          exact_mod_cast NNReal.coe_nonneg (F.probs y))) hα_pos
  have hdecomp' :
      sandwichedRenyiQ
          (State.cqConditioningState E).matrix
          (identityTensorStateMatrix (a := A)
            (F.cqState.reindex (Equiv.prodComm Y B)))
          (State.cqConditioningState E).pos
          (identityTensorStateMatrix_posSemidef_of_state (a := A)
            (F.cqState.reindex (Equiv.prodComm Y B))) α =
        ∑ y, sandwichedRenyiQ (conditionalRenyiBlock E y)
          ((F.probs y : ℂ) • identityTensorStateMatrix (a := A) (F.states y))
          (conditionalRenyiBlock_posSemidef E y)
          ((identityTensorStateMatrix_posSemidef_of_state
            (a := A) (F.states y)).smul (by
              exact_mod_cast NNReal.coe_nonneg (F.probs y))) α := by
    simpa only [conditionalRenyiState_eq_rightBlockDiagonal E,
      sandwiched_reference_cq_blockDiagonal F] using hdecomp
  rw [hdecomp']
  apply Finset.sum_congr rfl
  intro y hy
  have hscale := sandwichedQ_real_smul_left_right
    (E.states y).matrix
    (identityTensorStateMatrix (a := A) (F.states y))
      (E.states y).pos
      (identityTensorStateMatrix_posSemidef_of_state (a := A) (F.states y))
      (E.probs y) (F.probs y) hα_pos hα_ne_one
  simpa only [conditionalRenyiBlock_eq_weighted_state] using hscale

noncomputable def sandwichedUpFixedReferenceFormulaReal
    (E : Ensemble Y (A × B)) (F : Ensemble Y B) (α : ℝ) : ℝ :=
  (1 / (1 - α)) * log2
    (∑ y, (E.probs y : ℝ) ^ α * (F.probs y : ℝ) ^ (1 - α) *
      sandwichedRenyiQ (E.states y).matrix
        (identityTensorStateMatrix (a := A) (F.states y))
        (E.states y).pos
        (identityTensorStateMatrix_posSemidef_of_state
          (a := A) (F.states y)) α)

noncomputable def sandwichedFixedReferenceBranchValue
    (E : Ensemble Y (A × B)) (F : Ensemble Y B) (y : Y) (α : ℝ)
    (hF : (F.cqState.reindex (Equiv.prodComm Y B)).matrix.PosDef)
    (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  (E.states y).conditionalSandwichedRenyiUpSourceCandidate
    (F.states y) (sandwiched_reference_cq_state_posDef F hF y)
    α hα_pos hα_ne_one

noncomputable def sandwichedUpFixedReferenceBranchFormulaReal
    (E : Ensemble Y (A × B)) (F : Ensemble Y B) (α : ℝ)
    (hF : (F.cqState.reindex (Equiv.prodComm Y B)).matrix.PosDef)
    (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  (1 / (1 - α)) * log2
    (∑ y, (E.probs y : ℝ) ^ α * (F.probs y : ℝ) ^ (1 - α) *
      Real.rpow 2 ((1 - α) *
        sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one))

theorem sandwichedUpFixedReferenceFormulaReal_eq_branchFormula
    (E : Ensemble Y (A × B)) (F : Ensemble Y B)
    (hF : (F.cqState.reindex (Equiv.prodComm Y B)).matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedUpFixedReferenceFormulaReal E F α =
      sandwichedUpFixedReferenceBranchFormulaReal E F α hF hα_pos hα_ne_one := by
  unfold sandwichedUpFixedReferenceFormulaReal
    sandwichedUpFixedReferenceBranchFormulaReal
  apply congrArg (fun x : ℝ => (1 / (1 - α)) * log2 x)
  apply Finset.sum_congr rfl
  intro y hy
  have hyF : (F.states y).matrix.PosDef :=
    sandwiched_reference_cq_state_posDef F hF y
  have hQypos := sandwichedRenyiQ_pos_of_state_posDef_reference
    (E.states y)
    (identityTensorStateMatrix_posDef_of_posDef (a := A)
      (F.states y) hyF) α
  have htrace := conditionalSandwichedRenyiUpSourceCandidate_eq_traceTerm
    (E.states y) (F.states y) hyF α hα_pos hα_ne_one
  have htrace' :
      (E.states y).conditionalSandwichedRenyiUpSourceCandidate
          (F.states y) hyF α hα_pos hα_ne_one =
        -(1 / (α - 1)) * log2
          (sandwichedRenyiQ (E.states y).matrix
            (identityTensorStateMatrix (a := A) (F.states y))
            (E.states y).pos
            (identityTensorStateMatrix_posSemidef_of_state
              (a := A) (F.states y)) α) := by
    simpa [conditionalSandwichedRenyiUpSourceTraceTerm,
      sandwichedRenyiQ_eq_psdTracePower_referenceInner] using htrace
  have hpow :
      Real.rpow 2 ((1 - α) *
          (E.states y).conditionalSandwichedRenyiUpSourceCandidate
            (F.states y) hyF α hα_pos hα_ne_one) =
        sandwichedRenyiQ (E.states y).matrix
          (identityTensorStateMatrix (a := A) (F.states y))
          (E.states y).pos
          (identityTensorStateMatrix_posSemidef_of_state
            (a := A) (F.states y)) α := by
    rw [htrace']
    have harg : (1 - α) * (-(1 / (α - 1))) = 1 := by
      field_simp [hα_ne_one]
      ring
    have harg' :
        (1 - α) * (-(1 / (α - 1)) *
          log2 (sandwichedRenyiQ (E.states y).matrix
            (identityTensorStateMatrix (a := A) (F.states y))
            (E.states y).pos
            (identityTensorStateMatrix_posSemidef_of_state
              (a := A) (F.states y)) α)) =
          log2 (sandwichedRenyiQ (E.states y).matrix
            (identityTensorStateMatrix (a := A) (F.states y))
            (E.states y).pos
            (identityTensorStateMatrix_posSemidef_of_state
              (a := A) (F.states y)) α) := by
      calc
        _ = ((1 - α) * (-(1 / (α - 1)))) *
            log2 (sandwichedRenyiQ (E.states y).matrix
              (identityTensorStateMatrix (a := A) (F.states y))
              (E.states y).pos
              (identityTensorStateMatrix_posSemidef_of_state
                (a := A) (F.states y)) α) := by ring
        _ = _ := by rw [harg]; ring
    rw [harg']
    rw [QIT.rpow_two_log2_pos hQypos]
  simp only [sandwichedFixedReferenceBranchValue]
  rw [hpow]

theorem sandwichedRenyiPSDReferenceE_cq_fullrank_reference_formula
    (E : Ensemble Y (A × B)) (F : Ensemble Y B)
    (hF : (F.cqState.reindex (Equiv.prodComm Y B)).matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    -sandwichedRenyiPSDReferenceE
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A)
          (F.cqState.reindex (Equiv.prodComm Y B)))
        (identityTensorStateMatrix_posSemidef_of_state
          (a := A) (F.cqState.reindex (Equiv.prodComm Y B))) α =
      (sandwichedUpFixedReferenceFormulaReal E F α : EReal) := by
  let ρ := State.cqConditioningState E
  let σ := F.cqState.reindex (Equiv.prodComm Y B)
  have hτ : (identityTensorStateMatrix (a := A) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := A) σ hF
  have hQ : 0 < sandwichedRenyiQ ρ.matrix
      (identityTensorStateMatrix (a := A) σ) ρ.pos hτ.posSemidef α := by
    exact sandwichedRenyiQ_pos_of_state_posDef_reference ρ hτ α
  have hdecomp := sandwichedRenyiQ_cq_reference_decomposition
    (A := A) (B := B) (Y := Y) E F hα_pos hα_ne_one
  have hdecomp' :
      sandwichedRenyiQ ρ.matrix
          (identityTensorStateMatrix (a := A) σ) ρ.pos hτ.posSemidef α =
        ∑ y, (E.probs y : ℝ) ^ α * (F.probs y : ℝ) ^ (1 - α) *
          sandwichedRenyiQ (E.states y).matrix
            (identityTensorStateMatrix (a := A) (F.states y))
            (E.states y).pos
            (identityTensorStateMatrix_posSemidef_of_state
              (a := A) (F.states y)) α := by
    simpa [ρ, σ] using hdecomp
  have hbranch : ∀ y,
      0 < sandwichedRenyiQ (E.states y).matrix
        (identityTensorStateMatrix (a := A) (F.states y))
        (E.states y).pos
        (identityTensorStateMatrix_posSemidef_of_state
          (a := A) (F.states y)) α := by
    intro y
    have hyF : (F.states y).matrix.PosDef :=
      sandwiched_reference_cq_state_posDef F hF y
    exact sandwichedRenyiQ_pos_of_state_posDef_reference
      (E.states y)
      (identityTensorStateMatrix_posDef_of_posDef (a := A)
        (F.states y) hyF) α
  have hsum :
      0 < ∑ y, (E.probs y : ℝ) ^ α * (F.probs y : ℝ) ^ (1 - α) *
        sandwichedRenyiQ (E.states y).matrix
          (identityTensorStateMatrix (a := A) (F.states y))
          (E.states y).pos
          (identityTensorStateMatrix_posSemidef_of_state
            (a := A) (F.states y)) α := by
    rw [← hdecomp]
    exact hQ
  by_cases hα_lt_one : α < 1
  · rw [sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one _ _ hα_lt_one,
      sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero
        ρ (identityTensorStateMatrix_posSemidef_of_state (a := A) σ) α
        hQ.ne']
    unfold sandwichedRenyiPSDReferenceLowAlpha
      sandwichedUpFixedReferenceFormulaReal
    rw [hdecomp']
    rw [← EReal.coe_neg]
    apply EReal.coe_eq_coe_iff.mpr
    field_simp [hα_ne_one]
    ring
  · have hα_gt_one : 1 < α :=
      lt_of_le_of_ne (not_lt.mp hα_lt_one) hα_ne_one.symm
    have hsupport : Matrix.Supports ρ.matrix
        (identityTensorStateMatrix (a := A) σ) :=
      Matrix.Supports.of_right_posDef _ _ hτ
    rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ hα_gt_one,
      sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
        ρ hτ.posSemidef α hsupport]
    unfold sandwichedRenyiPSDReferenceHighAlphaFinite
      sandwichedUpFixedReferenceFormulaReal
    rw [← sandwichedRenyiQ_eq_psdTracePower_referenceInner
      ρ hτ.posSemidef α]
    rw [hdecomp']
    rw [← EReal.coe_neg]
    apply EReal.coe_eq_coe_iff.mpr
    field_simp [hα_ne_one]
    ring

private theorem sandwiched_down_normalized_q_pos
    (ρ : State (A × B)) (α : ℝ) :
    0 < sandwichedRenyiQ ρ.matrix
      (identityTensorStateMatrix (a := A) ρ.marginalB)
      ρ.pos
      (identityTensorStateMatrix_posSemidef_of_state (a := A) ρ.marginalB) α := by
  rw [sandwichedRenyiQ_eq_psdTracePower_referenceInner]
  have hSupport : Matrix.Supports ρ.matrix
      (identityTensorStateMatrix (a := A) ρ.marginalB) := by
    simpa [identityTensorStateMatrix] using
      (matrix_supports_identityTensor_marginalB ρ)
  exact sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports
    ρ (identityTensorStateMatrix_posSemidef_of_state (a := A) ρ.marginalB)
    hSupport α

/-- The real sandwiched down-arrow entropy of the normalized `y`-component. -/
noncomputable def sandwichedDownComponentEntropy
    (E : Ensemble Y (A × B)) (y : Y) (α : ℝ) : ℝ :=
  (1 / (1 - α)) * log2
    (sandwichedRenyiQ (E.states y).matrix
      (identityTensorStateMatrix (a := A) (E.states y).marginalB)
      (E.states y).pos
      (identityTensorStateMatrix_posSemidef_of_state
        (a := A) (E.states y).marginalB) α)

omit [DecidableEq Y] in
/-- Every normalized component has a strictly positive sandwiched `Q_α`. -/
theorem sandwichedDownComponentQ_pos
    (E : Ensemble Y (A × B)) (y : Y) (α : ℝ) :
    0 < sandwichedRenyiQ (E.states y).matrix
      (identityTensorStateMatrix (a := A) (E.states y).marginalB)
      (E.states y).pos
      (identityTensorStateMatrix_posSemidef_of_state
        (a := A) (E.states y).marginalB) α :=
  sandwiched_down_normalized_q_pos (E.states y) α

/-- The normalized global cq state has a strictly positive sandwiched `Q_α`. -/
theorem sandwichedDownClassicalQ_pos
    (E : Ensemble Y (A × B)) (α : ℝ) :
    0 < sandwichedRenyiQ
      (State.cqConditioningState E).matrix
      (identityTensorStateMatrix (a := A)
        (State.cqConditioningState E).marginalB)
      (State.cqConditioningState E).pos
      (identityTensorStateMatrix_posSemidef_of_state
        (a := A) (State.cqConditioningState E).marginalB) α :=
  sandwiched_down_normalized_q_pos (State.cqConditioningState E) α

omit [DecidableEq Y] in
/-- Exponentiating a normalized component entropy recovers its sandwiched
`Q_α` value. -/
theorem sandwichedDownComponentQ_eq_rpow_entropy
    (E : Ensemble Y (A × B)) (y : Y) (α : ℝ) (hα_ne_one : α ≠ 1) :
    Real.rpow 2 ((1 - α) * sandwichedDownComponentEntropy E y α) =
      sandwichedRenyiQ (E.states y).matrix
        (identityTensorStateMatrix (a := A) (E.states y).marginalB)
        (E.states y).pos
        (identityTensorStateMatrix_posSemidef_of_state
          (a := A) (E.states y).marginalB) α := by
  have hq := sandwichedDownComponentQ_pos E y α
  unfold sandwichedDownComponentEntropy
  have hcancel :
      (1 - α) * ((1 / (1 - α)) * log2
        (sandwichedRenyiQ (E.states y).matrix
          (identityTensorStateMatrix (a := A) (E.states y).marginalB)
          (E.states y).pos
          (identityTensorStateMatrix_posSemidef_of_state
            (a := A) (E.states y).marginalB) α)) =
        log2 (sandwichedRenyiQ (E.states y).matrix
          (identityTensorStateMatrix (a := A) (E.states y).marginalB)
          (E.states y).pos
          (identityTensorStateMatrix_posSemidef_of_state
            (a := A) (E.states y).marginalB) α) := by
    field_simp [hα_ne_one]
  rw [hcancel, QIT.rpow_two_log2_pos hq]

theorem sandwichedRenyiQ_classical_decomposition_lowAlpha
    (E : Ensemble Y (A × B)) {α : ℝ}
    (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ
        (State.cqConditioningState E).matrix
        (identityTensorStateMatrix (a := A)
          (State.cqConditioningState E).marginalB)
        (State.cqConditioningState E).pos
        (identityTensorStateMatrix_posSemidef_of_state
          (a := A) (State.cqConditioningState E).marginalB) α =
      ∑ y, (E.probs y : ℝ) *
        sandwichedRenyiQ (E.states y).matrix
          (identityTensorStateMatrix (a := A) (E.states y).marginalB)
          (E.states y).pos
          (identityTensorStateMatrix_posSemidef_of_state
            (a := A) (E.states y).marginalB) α := by
  have hstate := conditionalRenyiState_eq_rightBlockDiagonal E
  have href := sandwiched_conditionalReference_blockDiagonal E
  have hgeneric := sandwichedRenyiQ_fixedReference_blockDiagonal_lowAlpha
    (A := A) (B := B)
    (fun y => conditionalRenyiBlock E y)
    (fun y => (E.probs y : ℂ) • identityTensorStateMatrix (a := A)
      (E.states y).marginalB) (fun y => conditionalRenyiBlock_posSemidef E y)
    (fun y => by
      have hp : 0 ≤ (E.probs y : ℂ) := by
        exact_mod_cast NNReal.coe_nonneg (E.probs y)
      exact (identityTensorStateMatrix_posSemidef_of_state
        (a := A) (E.states y).marginalB).smul hp)
    hα_half hα_lt_one
  have hblock :
      sandwichedRenyiQ
          (State.cqConditioningState E).matrix
          (identityTensorStateMatrix (a := A)
            (State.cqConditioningState E).marginalB)
          (State.cqConditioningState E).pos
          (identityTensorStateMatrix_posSemidef_of_state
            (a := A) (State.cqConditioningState E).marginalB) α =
        ∑ y, sandwichedRenyiQ (conditionalRenyiBlock E y)
          ((E.probs y : ℂ) • identityTensorStateMatrix (a := A)
            (E.states y).marginalB)
          (conditionalRenyiBlock_posSemidef E y)
          (by
            have hp : 0 ≤ (E.probs y : ℂ) := by
              exact_mod_cast NNReal.coe_nonneg (E.probs y)
            exact (identityTensorStateMatrix_posSemidef_of_state
              (a := A) (E.states y).marginalB).smul hp) α := by
    simpa only [sandwichedRenyiQ, hstate, href] using hgeneric
  calc
    _ = ∑ y, sandwichedRenyiQ (conditionalRenyiBlock E y)
          ((E.probs y : ℂ) • identityTensorStateMatrix (a := A)
            (E.states y).marginalB)
          (conditionalRenyiBlock_posSemidef E y)
          (by
            have hp : 0 ≤ (E.probs y : ℂ) := by
              exact_mod_cast NNReal.coe_nonneg (E.probs y)
            exact (identityTensorStateMatrix_posSemidef_of_state
              (a := A) (E.states y).marginalB).smul hp) α := hblock
    _ = ∑ y, (E.probs y : ℝ) *
        sandwichedRenyiQ (E.states y).matrix
          (identityTensorStateMatrix (a := A) (E.states y).marginalB)
          (E.states y).pos
          (identityTensorStateMatrix_posSemidef_of_state
            (a := A) (E.states y).marginalB) α := by
      apply Finset.sum_congr rfl
      intro y hy
      simpa only [sandwichedRenyiQ,
        conditionalRenyiBlock_eq_weighted_state] using
        (sandwichedQ_real_smul_both
          (E.states y).matrix
          (identityTensorStateMatrix (a := A) (E.states y).marginalB)
          (E.states y).pos
          (identityTensorStateMatrix_posSemidef_of_state
            (a := A) (E.states y).marginalB)
          (E.probs y) (by linarith) hα_lt_one)

theorem sandwichedRenyiQ_classical_decomposition_lowAlpha_support
    (E : Ensemble Y (A × B)) {α : ℝ}
    (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ
        (State.cqConditioningState E).matrix
        (identityTensorStateMatrix (a := A)
          (State.cqConditioningState E).marginalB)
        (State.cqConditioningState E).pos
        (identityTensorStateMatrix_posSemidef_of_state
          (a := A) (State.cqConditioningState E).marginalB) α =
      E.conditionalRenyiSupport.sum (fun y =>
        (E.probs y : ℝ) *
          sandwichedRenyiQ (E.states y).matrix
            (identityTensorStateMatrix (a := A) (E.states y).marginalB)
            (E.states y).pos
            (identityTensorStateMatrix_posSemidef_of_state
              (a := A) (E.states y).marginalB) α) := by
  rw [sandwichedRenyiQ_classical_decomposition_lowAlpha E hα_half hα_lt_one]
  rw [show E.conditionalRenyiSupport =
      (Finset.univ : Finset Y).filter (fun y => E.probs y ≠ 0) by
    rfl]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hpy : E.probs y = 0
  · simp [hpy]
  · simp [hpy]

/-- The classical-conditioning `Q_α` decomposition across the complete source
range.  The zero-weight case is separated before combining real powers, so
the high-order negative exponent never creates an informal `0 * ∞` term. -/
theorem sandwichedRenyiQ_classical_decomposition_support_safe
    (E : Ensemble Y (A × B)) {α : ℝ}
    (hα_half : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyiQ
        (State.cqConditioningState E).matrix
        (identityTensorStateMatrix (a := A)
          (State.cqConditioningState E).marginalB)
        (State.cqConditioningState E).pos
        (identityTensorStateMatrix_posSemidef_of_state
          (a := A) (State.cqConditioningState E).marginalB) α =
      ∑ y, (E.probs y : ℝ) *
        sandwichedRenyiQ (E.states y).matrix
          (identityTensorStateMatrix (a := A) (E.states y).marginalB)
          (E.states y).pos
          (identityTensorStateMatrix_posSemidef_of_state
            (a := A) (E.states y).marginalB) α := by
  have hα_pos : 0 < α := by linarith
  have hdecomp := sandwichedRenyiQ_cq_reference_decomposition
    (A := A) (B := B) (Y := Y) E E.conditionalMarginalB
    hα_pos hα_ne_one
  rw [Ensemble.conditionalRenyiState_marginalB_eq_conditionalMarginalBYState]
  change sandwichedRenyiQ
      (State.cqConditioningState E).matrix
      (identityTensorStateMatrix (a := A)
        (E.conditionalMarginalB.cqState.reindex (Equiv.prodComm Y B)))
      (State.cqConditioningState E).pos
      (identityTensorStateMatrix_posSemidef_of_state
        (a := A) (E.conditionalMarginalB.cqState.reindex (Equiv.prodComm Y B))) α = _
  rw [hdecomp]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hpy : E.probs y = 0
  · simp [hpy, Real.zero_rpow hα_pos.ne']
  · have hp : 0 < (E.probs y : ℝ) := by
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hpy)
    rw [show (E.conditionalMarginalB.probs y : ℝ) = (E.probs y : ℝ) by rfl]
    rw [show E.conditionalMarginalB.states y = (E.states y).marginalB by rfl]
    rw [← Real.rpow_add hp]
    norm_num

noncomputable def sandwichedDownFiniteSupportQ
    (E : Ensemble Y (A × B)) (α : ℝ) : ℝ :=
  E.conditionalRenyiSupport.sum (fun y =>
    (E.probs y : ℝ) *
      sandwichedRenyiQ (E.states y).matrix
        (identityTensorStateMatrix (a := A) (E.states y).marginalB)
        (E.states y).pos
        (identityTensorStateMatrix_posSemidef_of_state
          (a := A) (E.states y).marginalB) α)

noncomputable def sandwichedDownFiniteSupportFormulaReal
    (E : Ensemble Y (A × B)) (α : ℝ) : ℝ :=
  (1 / (α - 1)) * log2 (sandwichedDownFiniteSupportQ E α)

theorem sandwichedDownFiniteSupportQ_eq_globalQ_lowAlpha
    (E : Ensemble Y (A × B)) {α : ℝ}
    (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1) :
    sandwichedDownFiniteSupportQ E α =
      sandwichedRenyiQ
        (State.cqConditioningState E).matrix
        (identityTensorStateMatrix (a := A)
          (State.cqConditioningState E).marginalB)
        (State.cqConditioningState E).pos
        (identityTensorStateMatrix_posSemidef_of_state
          (a := A) (State.cqConditioningState E).marginalB) α := by
  exact (sandwichedRenyiQ_classical_decomposition_lowAlpha_support
    E hα_half hα_lt_one).symm

theorem conditionalSandwichedRenyiDown_classicalConditioning_source_formula_of_lt_one
    (E : Ensemble Y (A × B)) (α : ℝ) (hα : 1 / 2 ≤ α)
    (hα_ne_one : α ≠ 1) (hα_lt_one : α < 1)
    (hQne : sandwichedRenyiQ
        (State.cqConditioningState E).matrix
        (identityTensorStateMatrix (a := A)
          (State.cqConditioningState E).marginalB)
        (State.cqConditioningState E).pos
        (identityTensorStateMatrix_posSemidef_of_state
          (a := A) (State.cqConditioningState E).marginalB) α ≠ 0) :
    conditionalSandwichedRenyiDownE E α hα hα_ne_one =
      (-(sandwichedDownFiniteSupportFormulaReal E α) : EReal) := by
  unfold conditionalSandwichedRenyiDownE
  rw [sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one _ _ hα_lt_one,
    sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero
      _ _ _ hQne]
  unfold sandwichedRenyiPSDReferenceLowAlpha
    sandwichedDownFiniteSupportFormulaReal
  rw [sandwichedDownFiniteSupportQ_eq_globalQ_lowAlpha E hα hα_lt_one]


end State

end

end QIT
