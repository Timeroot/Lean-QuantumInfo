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
public import QIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.LowAlphaQDecomposition
public import QIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.HighAlphaSupport
public import QIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.ScalarOptimizer
public import QIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.RegularizedSourceWrappers

/-!
# public source-shaped wrappers (arbitrary reference)

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

/-! The high-order source branch uses the same normalized full-rank path as the
low-order branch.  The support hypothesis is kept explicit so that no
undefined zero-eigenvalue power is introduced at the limiting reference. -/

theorem conditionalSandwichedRenyiUp_candidateE_fullRankApprox_tendsto_of_highAlpha
    [Nonempty B]
    (E : Ensemble Y (A × B)) (σ : State (B × Y)) (α : ℝ)
    (hα_gt_one : 1 < α)
    (hSupport : Matrix.Supports
      (State.cqConditioningState E).matrix
      (identityTensorStateMatrix (a := A) σ)) :
    Filter.Tendsto
      (fun δ : ℝ =>
        -sandwichedRenyiPSDReferenceE
          (State.cqConditioningState E)
          (identityTensorStateMatrix (a := A)
            (fullRankApproxMaximallyMixedStatePath σ δ))
          (identityTensorStateMatrix_posSemidef_of_state (a := A)
            (fullRankApproxMaximallyMixedStatePath σ δ)) α)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1))
      (nhds (-sandwichedRenyiPSDReferenceE
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ) α)) := by
  classical
  letI : Nonempty Y := Ensemble.index_nonempty E
  letI : Nonempty (B × Y) := inferInstance
  let ρ := State.cqConditioningState E
  let τ := identityTensorStateMatrix (a := A) σ
  let hτ : τ.PosSemidef := identityTensorStateMatrix_posSemidef_of_state (a := A) σ
  let ε : ℝ → ℝ := fun δ =>
    δ / ((1 - δ) * (Fintype.card (B × Y) : ℝ))
  let scale : ℝ → ℝ := fun δ => 1 - δ
  have hε := fullRankApproxMaximallyMixedRegularizationParameter_tendsto_zero
    (a := B × Y)
  have hhigh :=
    sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve_tendsto_of_supports
      ρ hτ hSupport α hα_gt_one
  have hreal :
      Filter.Tendsto
        (fun δ : ℝ =>
          -(sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve
            ρ hτ α (ε δ)) + log2 (scale δ))
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 1))
        (nhds (-sandwichedRenyiPSDReferenceHighAlphaFinite ρ τ hτ α)) := by
    have hhigh' := hhigh.comp hε
    have hlog : Filter.Tendsto (fun δ : ℝ => log2 (scale δ))
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds 0) := by
      simpa [scale] using log2_one_sub_tendsto_zero
    have hneg := hhigh'.neg
    convert hneg.add hlog using 1
    all_goals simp [ρ, τ]
  have hevent : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioo 0 1),
      0 < δ ∧ δ < 1 := self_mem_nhdsWithin
  have hpath : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioo 0 1),
      (fun δ : ℝ =>
        -sandwichedRenyiPSDReferenceE ρ
          (identityTensorStateMatrix (a := A)
            (fullRankApproxMaximallyMixedStatePath σ δ))
            (identityTensorStateMatrix_posSemidef_of_state (a := A)
            (fullRankApproxMaximallyMixedStatePath σ δ)) α) δ =
        ((-(sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve
            ρ hτ α (ε δ)) + log2 (scale δ) : ℝ) : EReal) := by
    filter_upwards [hevent] with δ hδ
    have hscale_pos : 0 < scale δ := by dsimp [scale]; linarith
    have hε_pos : 0 < ε δ := by
      dsimp [ε]
      have hcard_pos : 0 < (Fintype.card (B × Y) : ℝ) := by
        exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance)
      exact div_pos hδ.1 (mul_pos (sub_pos.mpr hδ.2) hcard_pos)
    have hε_nonneg : 0 ≤ ε δ := hε_pos.le
    have hpath_matrix :=
      fullRankApproxMaximallyMixedStatePath_matrix_eq_smul_referenceRegularization
        σ hδ
    have hmatrix :
        identityTensorStateMatrix (a := A)
          (fullRankApproxMaximallyMixedStatePath σ δ) =
          scale δ • sandwichedRenyiReferenceRegularization τ (ε δ) := by
      change Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix A)
        (fullRankApproxMaximallyMixedStatePath σ δ).matrix = _
      rw [hpath_matrix]
      calc
        Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix A)
              (((1 - δ : ℝ) : ℂ) •
                sandwichedRenyiReferenceRegularization σ.matrix
                  (δ / ((1 - δ) * (Fintype.card (B × Y) : ℝ)))) =
            Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix A)
              ((1 - δ) • sandwichedRenyiReferenceRegularization σ.matrix
                (δ / ((1 - δ) * (Fintype.card (B × Y) : ℝ)))) := by
          ext i j
          simp [Matrix.smul_apply]
        _ = (1 - δ) • Matrix.kroneckerMap (fun x y => x * y)
              (1 : CMatrix A)
              (sandwichedRenyiReferenceRegularization σ.matrix
                (δ / ((1 - δ) * (Fintype.card (B × Y) : ℝ)))) := by
          exact kroneckerMap_one_real_smul (A := A) (B := B) (Y := Y)
            (1 - δ) _
        _ = scale δ • sandwichedRenyiReferenceRegularization τ (ε δ) := by
          simp [τ, ε, scale, sandwichedRenyiReferenceRegularization,
            identityTensorStateMatrix, kroneckerMap_one_add, smul_smul]
          rw [kroneckerMap_one_smul_real, kroneckerMap_one_one]
          ext i j
          simp [Matrix.smul_apply]
          field_simp [ne_of_gt hscale_pos]
    have hpath_pd :
        (fullRankApproxMaximallyMixedStatePath σ δ).matrix.PosDef := by
      simpa [fullRankApproxMaximallyMixedStatePath, fullRankApproxStatePath,
        hδ] using
        (fullRankApproxState_posDef_of_noise σ
          (State.maximallyMixed (B × Y))
          (State.maximallyMixed_posDef)
          hδ.1.le hδ.2.le hδ.1)
    have href_pd :
        (identityTensorStateMatrix (a := A)
          (fullRankApproxMaximallyMixedStatePath σ δ)).PosDef :=
      identityTensorStateMatrix_posDef_of_posDef (a := A)
        (fullRankApproxMaximallyMixedStatePath σ δ) hpath_pd
    have hpath_support : Matrix.Supports ρ.matrix
        (identityTensorStateMatrix (a := A)
          (fullRankApproxMaximallyMixedStatePath σ δ)) :=
      Matrix.Supports.of_right_posDef _ _ href_pd
    rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ hα_gt_one,
      sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
        ρ href_pd.posSemidef α hpath_support]
    have hreg_pd := sandwichedRenyiReferenceRegularization_posDef hτ hε_pos
    have hfinite_eq :
        sandwichedRenyiPSDReferenceHighAlphaFinite ρ
            (identityTensorStateMatrix (a := A)
              (fullRankApproxMaximallyMixedStatePath σ δ))
            href_pd.posSemidef α =
          sandwichedRenyiPSDReferenceHighAlphaFinite ρ
            (scale δ • sandwichedRenyiReferenceRegularization τ (ε δ))
            (Matrix.PosSemidef.smul hreg_pd.posSemidef
              (by exact_mod_cast hscale_pos.le)) α := by
      simp only [hmatrix]
    rw [hfinite_eq]
    have hscale :=
      sandwichedRenyiPSDReferenceHighAlphaFinite_real_smul_reference
        ρ hreg_pd hscale_pos α hα_gt_one
    rw [hscale]
    simp [sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve,
      hε_pos, scale, sub_eq_add_neg, add_comm]
    have hneg : ∀ x y : ℝ,
        -((-y : EReal) + (x : EReal)) =
          (y : EReal) + (-x : EReal) := by
      intro x y
      have hy : (-((y : EReal)) : EReal) = ((-y : ℝ) : EReal) :=
        (EReal.coe_neg y).symm
      have hx : (-((x : EReal)) : EReal) = ((-x : ℝ) : EReal) :=
        (EReal.coe_neg x).symm
      rw [hy, hx, ← EReal.coe_add, ← EReal.coe_neg]
      congr 1
      ring
    exact hneg _ _
  have htarget :
      -sandwichedRenyiPSDReferenceE ρ τ hτ α =
        (-sandwichedRenyiPSDReferenceHighAlphaFinite ρ τ hτ α : EReal) := by
    rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ hα_gt_one,
      sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
        ρ hτ α hSupport]
  rw [htarget]
  have hpath' := hpath.mono (fun _ h => h.symm)
  exact Filter.Tendsto.congr' hpath' (EReal.tendsto_coe.mpr hreal)

/-! Pinching closes the non-singular arbitrary-reference branch. -/
theorem sandwichedRenyiPSDReferenceE_arbitrary_reference_le_classicalFormula_of_half_lt_lt_one_of_coordinateYPinched_posDef
    [Nonempty B]
    (E : Ensemble Y (A × B)) (σ : State (B × Y))
    (hF : ((coordinateYPinchedEnsemble (B := B) (Y := Y) σ).cqState.reindex
      (Equiv.prodComm Y B)).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    -sandwichedRenyiPSDReferenceE
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ) α ≤
      (sandwichedUpClassicalFormulaReal E α hα_half.le
        (ne_of_lt hα_lt_one) : EReal) := by
  have hpinch := conditionalSandwichedRenyiUp_candidate_le_of_coordinateYPinching
    E σ α hα_half.le (ne_of_lt hα_lt_one)
  have hclassical :=
    sandwichedRenyiPSDReferenceE_cq_fullrank_reference_le_classicalFormula_of_half_lt_lt_one
      E (coordinateYPinchedEnsemble (B := B) (Y := Y) σ) hF α hα_half hα_lt_one
  have hclassical' :
      -sandwichedRenyiPSDReferenceE
          (State.cqConditioningState E)
          (identityTensorStateMatrix (a := A) (coordinateYPinchedState σ))
          (identityTensorStateMatrix_posSemidef_of_state
            (a := A) (coordinateYPinchedState σ)) α ≤
        (sandwichedUpClassicalFormulaReal E α hα_half.le
          (ne_of_lt hα_lt_one) : EReal) := by
    simpa only [coordinateYPinchedEnsemble_cqState_reindex] using hclassical
  exact hpinch.trans hclassical'

theorem sandwichedRenyiPSDReferenceE_cq_fullrank_reference_le_classicalFormula_of_one_lt
    (E : Ensemble Y (A × B)) (F : Ensemble Y B)
    (hF : (F.cqState.reindex (Equiv.prodComm Y B)).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    -sandwichedRenyiPSDReferenceE
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A)
          (F.cqState.reindex (Equiv.prodComm Y B)))
        (identityTensorStateMatrix_posSemidef_of_state
          (a := A) (F.cqState.reindex (Equiv.prodComm Y B))) α ≤
      (sandwichedUpClassicalFormulaReal E α (by linarith)
        (ne_of_gt hα_gt_one) : EReal) := by
  classical
  have hα_half : 1 / 2 < α := by linarith
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_gt_one
  have hα_ne_one : α ≠ 1 := ne_of_gt hα_gt_one
  have hq_pos : ∀ y, 0 < (F.probs y : ℝ) := by
    intro y
    exact_mod_cast sandwiched_reference_cq_prob_pos F hF y
  have hq_nonneg : ∀ y, 0 ≤ (F.probs y : ℝ) := by
    intro y
    exact (hq_pos y).le
  have hq_sum : ∑ y, (F.probs y : ℝ) = 1 := by
    exact_mod_cast F.weights_sum
  have hp_sum : ∑ y, (E.probs y : ℝ) = 1 := by
    exact_mod_cast E.weights_sum
  have hp_exists : ∃ y, 0 < (E.probs y : ℝ) := by
    by_contra h
    push Not at h
    have hp_zero : ∀ y, (E.probs y : ℝ) = 0 := by
      intro y
      exact le_antisymm (h y) (E.prob_nonneg y)
    have : ∑ y, (E.probs y : ℝ) = 0 := by
      simp [hp_zero]
    linarith
  have hbranch_le : ∀ y,
      sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one ≤
        sandwichedConditionalBranch E y α (by linarith) hα_ne_one := by
    intro y
    have hyF : (F.states y).matrix.PosDef :=
      sandwiched_reference_cq_state_posDef F hF y
    have hsource_bdd :=
      (E.states y).conditionalSandwichedRenyiUpSourceValueSet_bddAbove_of_one_lt
        hα_gt_one
    have hcandidate :
        (E.states y).conditionalSandwichedRenyiUpSourceCandidate
            (F.states y) hyF α hα_pos hα_ne_one ≤
          (E.states y).conditionalSandwichedRenyiUpSource α hα_pos hα_ne_one := by
      exact le_csSup hsource_bdd ⟨F.states y, hyF, rfl⟩
    calc
      sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one =
          (E.states y).conditionalSandwichedRenyiUpSourceCandidate
            (F.states y) hyF α hα_pos hα_ne_one := rfl
      _ ≤ (E.states y).conditionalSandwichedRenyiUpSource α hα_pos hα_ne_one :=
        hcandidate
      _ = sandwichedConditionalBranch E y α (by linarith) hα_ne_one := by
        symm
        exact conditionalSandwichedRenyiUpFiniteOrder_of_pos_ne_one_ne_half
          (E.states y) hα_pos hα_ne_one (by linarith)
  let k : ℝ := (1 - α) / α
  let c : Y → ℝ := fun y =>
    sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one
  let h : Y → ℝ := fun y =>
    sandwichedConditionalBranch E y α (by linarith) hα_ne_one
  let r : Y → ℝ := fun y =>
    (E.probs y : ℝ) * Real.rpow 2 (k * c y)
  let R : Y → ℝ := fun y =>
    (E.probs y : ℝ) * Real.rpow 2 (k * h y)
  have hk_neg : k ≤ 0 := by
    dsimp [k]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hα_pos.le
  have hr_nonneg : ∀ y, 0 ≤ r y := by
    intro y
    dsimp [r]
    exact mul_nonneg (E.prob_nonneg y) (Real.rpow_nonneg (by norm_num) _)
  have hR_nonneg : ∀ y, 0 ≤ R y := by
    intro y
    dsimp [R]
    exact mul_nonneg (E.prob_nonneg y) (Real.rpow_nonneg (by norm_num) _)
  have hR_le_r : ∀ y, R y ≤ r y := by
    intro y
    have hexp : k * h y ≤ k * c y := by
      exact mul_le_mul_of_nonpos_left (hbranch_le y) hk_neg
    have hpow : Real.rpow 2 (k * h y) ≤ Real.rpow 2 (k * c y) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    dsimp [r, R]
    exact mul_le_mul_of_nonneg_left hpow (E.prob_nonneg y)
  have hsum_le : (∑ y, R y) ≤ ∑ y, r y := by
    exact Finset.sum_le_sum fun y _ => hR_le_r y
  have hR_pos : 0 < ∑ y, R y := by
    apply Finset.sum_pos'
    · intro y hy
      exact hR_nonneg y
    · rcases hp_exists with ⟨y, hy⟩
      refine ⟨y, Finset.mem_univ y, ?_⟩
      dsimp [R]
      exact mul_pos hy (Real.rpow_pos_of_pos (by norm_num) _)
  have hr_pos : 0 < ∑ y, r y := hR_pos.trans_le hsum_le
  have hzero : ∀ y, (F.probs y : ℝ) = 0 → r y = 0 := by
    intro y hqy
    exfalso
    exact (ne_of_gt (hq_pos y)) hqy
  have hscalar_pos :
      0 < sandwichedScalarPower r (fun y => (F.probs y : ℝ)) α := by
    unfold sandwichedScalarPower
    apply Finset.sum_pos'
    · intro y hy
      exact mul_nonneg
        (Real.rpow_nonneg (hr_nonneg y) _)
        (Real.rpow_nonneg (le_of_lt (hq_pos y)) _)
    · rcases hp_exists with ⟨y, hy⟩
      refine ⟨y, Finset.mem_univ y, ?_⟩
      have hry : 0 < r y := by
        dsimp [r]
        exact mul_pos hy (Real.rpow_pos_of_pos (by norm_num) _)
      exact mul_pos
        (Real.rpow_pos_of_pos hry α)
        (Real.rpow_pos_of_pos (hq_pos y) (1 - α))
  have hscalar := sum_rpow_le_sandwichedScalarPower_of_nonneg
    r (fun y => (F.probs y : ℝ)) α hr_nonneg hq_nonneg hq_sum hzero hα_gt_one
  have hsum_pow : (∑ y, R y) ^ α ≤ (∑ y, r y) ^ α :=
    Real.rpow_le_rpow hR_pos.le hsum_le hα_pos.le
  have hscalar_le : (∑ y, R y) ^ α ≤
      sandwichedScalarPower r (fun y => (F.probs y : ℝ)) α :=
    hsum_pow.trans hscalar
  have hlog_le : log2 ((∑ y, R y) ^ α) ≤
      log2 (sandwichedScalarPower r (fun y => (F.probs y : ℝ)) α) := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (Real.rpow_pos_of_pos hR_pos α) hscalar_le)
      (le_of_lt (Real.log_pos (by norm_num)))
  have hlog_pow : log2 ((∑ y, R y) ^ α) =
      α * log2 (∑ y, R y) := by
    unfold log2
    rw [Real.log_rpow hR_pos]
    ring
  have hreal :
      (1 / (1 - α)) *
          log2 (sandwichedScalarPower r (fun y => (F.probs y : ℝ)) α) ≤
        (α / (1 - α)) * log2 (∑ y, R y) := by
    have hcoeff : 1 / (1 - α) ≤ 0 := by
      exact one_div_nonpos.mpr (by linarith)
    have h := mul_le_mul_of_nonpos_left hlog_le hcoeff
    rw [hlog_pow] at h
    calc
      (1 / (1 - α)) *
          log2 (sandwichedScalarPower r (fun y => (F.probs y : ℝ)) α) ≤
          (1 / (1 - α)) * (α * log2 (∑ y, R y)) := h
      _ = (α / (1 - α)) * log2 (∑ y, R y) := by ring
  rw [sandwichedRenyiPSDReferenceE_cq_fullrank_reference_formula
    E F hF α hα_pos hα_ne_one]
  apply EReal.coe_le_coe_iff.mpr
  rw [sandwichedUpFixedReferenceFormulaReal_eq_branchFormula
    E F hF α hα_pos hα_ne_one]
  rw [sandwichedUpFixedReferenceBranchFormulaReal_eq_log_scalarPower
    E F hF α hα_pos hα_ne_one]
  have hsupport_sum :
      (∑ y ∈ E.conditionalRenyiSupport,
        (E.probs y : ℝ) * Real.rpow 2 (k * h y)) =
        ∑ y, R y := by
    rw [← Finset.sum_subset (Finset.subset_univ
      E.conditionalRenyiSupport)]
    intro y hy hnot
    have hpy : E.probs y = 0 :=
      (E.not_mem_conditionalRenyiSupport_iff y).mp hnot
    dsimp [R]
    have hpy' : (E.probs y : ℝ) = 0 := by exact_mod_cast hpy
    simp [hpy]
  unfold sandwichedUpClassicalFormulaReal
  rw [hsupport_sum]
  simpa [h, R, r, k, c] using hreal

theorem sandwichedRenyiPSDReferenceE_arbitrary_reference_le_classicalFormula_of_one_lt_of_coordinateYPinched_posDef
    [Nonempty B]
    (E : Ensemble Y (A × B)) (σ : State (B × Y))
    (hF : ((coordinateYPinchedEnsemble (B := B) (Y := Y) σ).cqState.reindex
      (Equiv.prodComm Y B)).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    -sandwichedRenyiPSDReferenceE
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ) α ≤
      (sandwichedUpClassicalFormulaReal E α (by linarith)
        (ne_of_gt hα_gt_one) : EReal) := by
  have hpinch := conditionalSandwichedRenyiUp_candidate_le_of_coordinateYPinching
    E σ α (by linarith) (ne_of_gt hα_gt_one)
  have hclassical :=
    sandwichedRenyiPSDReferenceE_cq_fullrank_reference_le_classicalFormula_of_one_lt
      E (coordinateYPinchedEnsemble (B := B) (Y := Y) σ) hF α hα_gt_one
  have hclassical' :
      -sandwichedRenyiPSDReferenceE
          (State.cqConditioningState E)
          (identityTensorStateMatrix (a := A) (coordinateYPinchedState σ))
          (identityTensorStateMatrix_posSemidef_of_state
            (a := A) (coordinateYPinchedState σ)) α ≤
        (sandwichedUpClassicalFormulaReal E α (by linarith)
          (ne_of_gt hα_gt_one) : EReal) := by
    simpa only [coordinateYPinchedEnsemble_cqState_reindex] using hclassical
  exact hpinch.trans hclassical'

theorem sandwichedRenyiPSDReferenceE_arbitrary_reference_le_classicalFormula_of_one_lt
    [Nonempty B]
    (E : Ensemble Y (A × B)) (σ : State (B × Y))
    (α : ℝ) (hα_gt_one : 1 < α) :
    -sandwichedRenyiPSDReferenceE
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ) α ≤
      (sandwichedUpClassicalFormulaReal E α (by linarith)
        (ne_of_gt hα_gt_one) : EReal) := by
  classical
  letI : Nonempty Y := Ensemble.index_nonempty E
  let σc := coordinateYPinchedState σ
  have hpinch := conditionalSandwichedRenyiUp_candidate_le_of_coordinateYPinching
    E σ α (by linarith) (ne_of_gt hα_gt_one)
  have hc_le :
      -sandwichedRenyiPSDReferenceE
          (State.cqConditioningState E)
          (identityTensorStateMatrix (a := A) σc)
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σc) α ≤
        (sandwichedUpClassicalFormulaReal E α (by linarith)
          (ne_of_gt hα_gt_one) : EReal) := by
    by_cases hSupport : Matrix.Supports
        (State.cqConditioningState E).matrix
        (identityTensorStateMatrix (a := A) σc)
    · have htend :=
        conditionalSandwichedRenyiUp_candidateE_fullRankApprox_tendsto_of_highAlpha
          E σc α hα_gt_one hSupport
      have hevent : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioo 0 1),
          -sandwichedRenyiPSDReferenceE
              (State.cqConditioningState E)
              (identityTensorStateMatrix (a := A)
                (fullRankApproxMaximallyMixedStatePath σc δ))
              (identityTensorStateMatrix_posSemidef_of_state (a := A)
                (fullRankApproxMaximallyMixedStatePath σc δ)) α ≤
            (sandwichedUpClassicalFormulaReal E α (by linarith)
              (ne_of_gt hα_gt_one) : EReal) := by
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        have hF := coordinateYPinchedFullRankPath_posDef σ hδ
        have hF' :
            ((coordinateYPinchedEnsemble (B := B) (Y := Y)
              (fullRankApproxMaximallyMixedStatePath σc δ)).cqState.reindex
                (Equiv.prodComm Y B)).matrix.PosDef := by
          simpa [fullRankApproxMaximallyMixedStatePath,
            fullRankApproxStatePath, hδ,
            coordinateYPinchedState_regularized_maximallyMixed_fixed,
            coordinateYPinchedState_fixed] using hF
        have hclass :=
          sandwichedRenyiPSDReferenceE_cq_fullrank_reference_le_classicalFormula_of_one_lt
            E (coordinateYPinchedEnsemble (B := B) (Y := Y)
              (fullRankApproxMaximallyMixedStatePath σc δ)) hF' α hα_gt_one
        rw [coordinateYPinchedEnsemble_cqState_reindex] at hclass
        have hfixed :
            coordinateYPinchedState
                (fullRankApproxMaximallyMixedStatePath σc δ) =
              fullRankApproxMaximallyMixedStatePath σc δ := by
          have hσc_fixed : coordinateYPinchedState σc = σc := by
            simpa [σc] using coordinateYPinchedState_fixed σ
          simpa [σc, hσc_fixed, fullRankApproxMaximallyMixedStatePath,
            fullRankApproxStatePath, hδ] using
            (coordinateYPinchedState_regularized_maximallyMixed_fixed
              σc δ hδ.1.le hδ.2.le)
        simpa [hfixed] using hclass
      haveI : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) :=
        left_nhdsWithin_Ioo_neBot zero_lt_one
      exact le_of_tendsto htend hevent
    · rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ hα_gt_one,
      sandwichedRenyiPSDReferenceHighAlphaE_eq_top_of_not_supports
        _ (identityTensorStateMatrix_posSemidef_of_state (a := A) σc)
        α hSupport]
      simp
  exact hpinch.trans hc_le

theorem sandwichedRenyiPSDReferenceE_arbitrary_reference_le_classicalFormula_half_of_coordinateYPinched_posDef
    [Nonempty B]
    (E : Ensemble Y (A × B)) (σ : State (B × Y))
    (hF : ((coordinateYPinchedEnsemble (B := B) (Y := Y) σ).cqState.reindex
      (Equiv.prodComm Y B)).matrix.PosDef) :
    -sandwichedRenyiPSDReferenceE
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
        (1 / 2 : ℝ) ≤
      (sandwichedUpClassicalFormulaReal E (1 / 2 : ℝ) (by norm_num)
        (by norm_num) : EReal) := by
  have hpinch := conditionalSandwichedRenyiUp_candidate_le_of_coordinateYPinching
    E σ (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hclassical :=
    sandwichedRenyiPSDReferenceE_cq_fullrank_reference_le_classicalFormula_half
      E (coordinateYPinchedEnsemble (B := B) (Y := Y) σ) hF
  have hclassical' :
      -sandwichedRenyiPSDReferenceE
          (State.cqConditioningState E)
          (identityTensorStateMatrix (a := A) (coordinateYPinchedState σ))
          (identityTensorStateMatrix_posSemidef_of_state
            (a := A) (coordinateYPinchedState σ)) (1 / 2 : ℝ) ≤
        (sandwichedUpClassicalFormulaReal E (1 / 2 : ℝ) (by norm_num)
          (by norm_num) : EReal) := by
    simpa only [coordinateYPinchedEnsemble_cqState_reindex] using hclassical
  exact hpinch.trans hclassical'

theorem sandwichedRenyiPSDReferenceE_arbitrary_reference_le_classicalFormula_of_half_lt_lt_one
    [Nonempty B]
    (E : Ensemble Y (A × B)) (σ : State (B × Y))
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    -sandwichedRenyiPSDReferenceE
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ) α ≤
      (sandwichedUpClassicalFormulaReal E α hα_half.le
        (ne_of_lt hα_lt_one) : EReal) := by
  classical
  let σc := coordinateYPinchedState σ
  have hpinch := conditionalSandwichedRenyiUp_candidate_le_of_coordinateYPinching
    E σ α hα_half.le (ne_of_lt hα_lt_one)
  have hQzero_or_pos :
      sandwichedRenyiQ (State.cqConditioningState E).matrix
          (identityTensorStateMatrix (a := A) σc)
          (State.cqConditioningState E).pos
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σc) α = 0 ∨
        0 < sandwichedRenyiQ (State.cqConditioningState E).matrix
          (identityTensorStateMatrix (a := A) σc)
          (State.cqConditioningState E).pos
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σc) α := by
    have hnonneg := sandwichedRenyiQ_nonneg (State.cqConditioningState E).pos
      (identityTensorStateMatrix_posSemidef_of_state (a := A) σc) α
    rcases lt_or_eq_of_le hnonneg with hpos | hzero
    · exact Or.inr hpos
    · exact Or.inl hzero.symm
  have hc_le :
      -sandwichedRenyiPSDReferenceE
          (State.cqConditioningState E)
          (identityTensorStateMatrix (a := A) σc)
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σc) α ≤
        (sandwichedUpClassicalFormulaReal E α hα_half.le
          (ne_of_lt hα_lt_one) : EReal) := by
    rcases hQzero_or_pos with hQzero | hQpos
    · rw [sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one _ _ hα_lt_one,
        sandwichedRenyiPSDReferenceLowAlphaE_eq_top_of_Q_eq_zero
          _ _ _ hQzero]
      simp
    · let path : ℝ → State (B × Y) := fun δ =>
        fullRankApproxMaximallyMixedStatePath σc δ
      have htend :=
        conditionalSandwichedRenyiUp_candidateE_fullRankApprox_tendsto_of_lowAlpha
          E σc α hα_half hα_lt_one hQpos
      have hevent : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioo 0 1),
          -sandwichedRenyiPSDReferenceE
              (State.cqConditioningState E)
              (identityTensorStateMatrix (a := A) (path δ))
              (identityTensorStateMatrix_posSemidef_of_state (a := A) (path δ)) α ≤
            (sandwichedUpClassicalFormulaReal E α hα_half.le
              (ne_of_lt hα_lt_one) : EReal) := by
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        have hF := coordinateYPinchedFullRankPath_posDef σ hδ
        have hF' :
            ((coordinateYPinchedEnsemble (B := B) (Y := Y) (path δ)).cqState.reindex
              (Equiv.prodComm Y B)).matrix.PosDef := by
          simpa [path, σc, coordinateYPinchedState_fixed] using hF
        exact sandwichedRenyiPSDReferenceE_arbitrary_reference_le_classicalFormula_of_half_lt_lt_one_of_coordinateYPinched_posDef
          E (path δ) hF' α hα_half hα_lt_one
      haveI : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) :=
        left_nhdsWithin_Ioo_neBot zero_lt_one
      have hc_le' := le_of_tendsto htend hevent
      exact hc_le'
  exact hpinch.trans hc_le


theorem sandwichedRenyiPSDReferenceE_arbitrary_reference_le_classicalFormula_half
    [Nonempty B]
    (E : Ensemble Y (A × B)) (σ : State (B × Y)) :
    -sandwichedRenyiPSDReferenceE
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
        (1 / 2 : ℝ) ≤
      (sandwichedUpClassicalFormulaReal E (1 / 2 : ℝ) (by norm_num)
        (by norm_num) : EReal) := by
  classical
  letI : Nonempty Y := Ensemble.index_nonempty E
  letI : Nonempty (B × Y) := inferInstance
  let σc := coordinateYPinchedState σ
  have hpinch := conditionalSandwichedRenyiUp_candidate_le_of_coordinateYPinching
    E σ (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hQzero_or_pos :
      sandwichedRenyiQ (State.cqConditioningState E).matrix
          (identityTensorStateMatrix (a := A) σc)
          (State.cqConditioningState E).pos
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σc)
          (1 / 2 : ℝ) = 0 ∨
        0 < sandwichedRenyiQ (State.cqConditioningState E).matrix
          (identityTensorStateMatrix (a := A) σc)
          (State.cqConditioningState E).pos
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σc)
          (1 / 2 : ℝ) := by
    have hnonneg := sandwichedRenyiQ_nonneg (State.cqConditioningState E).pos
      (identityTensorStateMatrix_posSemidef_of_state (a := A) σc)
      (1 / 2 : ℝ)
    rcases lt_or_eq_of_le hnonneg with hpos | hzero
    · exact Or.inr hpos
    · exact Or.inl hzero.symm
  have hc_le :
      -sandwichedRenyiPSDReferenceE
          (State.cqConditioningState E)
          (identityTensorStateMatrix (a := A) σc)
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σc)
          (1 / 2 : ℝ) ≤
        (sandwichedUpClassicalFormulaReal E (1 / 2 : ℝ) (by norm_num)
          (by norm_num) : EReal) := by
    rcases hQzero_or_pos with hQzero | hQpos
    · rw [sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one _ _ (by norm_num),
        sandwichedRenyiPSDReferenceLowAlphaE_eq_top_of_Q_eq_zero
          _ _ _ hQzero]
      simp
    · let path : ℝ → State (B × Y) := fun δ =>
        fullRankApproxMaximallyMixedStatePath σc δ
      let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioo 0 1)
      have hmatrix :
          Filter.Tendsto
            (fun δ : ℝ => (path δ).matrix) l (nhds σc.matrix) := by
        refine Filter.Tendsto.congr' ?_
          (fullRankApproxMatrix_tendsto_zero σc
            (State.maximallyMixed (B × Y)))
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        change fullRankApproxMatrix σc
            (State.maximallyMixed (B × Y)) δ = _
        dsimp [path, fullRankApproxMaximallyMixedStatePath,
          fullRankApproxStatePath]
        rw [dif_pos hδ]
        rfl
      have hreference :
          Filter.Tendsto
            (fun δ : ℝ => identityTensorStateMatrix (a := A) (path δ)) l
            (nhds (identityTensorStateMatrix (a := A) σc)) := by
        apply tendsto_pi_nhds.2
        intro i
        apply tendsto_pi_nhds.2
        intro j
        simp only [identityTensorStateMatrix]
        have hi := (continuous_apply i.2).tendsto σc.matrix |>.comp hmatrix
        have hij := (continuous_apply j.2).tendsto (σc.matrix i.2) |>.comp hi
        have hc : Filter.Tendsto (fun _ : ℝ => (1 : CMatrix A) i.1 j.1)
            l (nhds ((1 : CMatrix A) i.1 j.1)) := tendsto_const_nhds
        simpa using hc.mul hij
      have hQ_tend :
          Filter.Tendsto
            (fun δ : ℝ => sandwichedRenyiQ
              (State.cqConditioningState E).matrix
              (identityTensorStateMatrix (a := A) (path δ))
              (State.cqConditioningState E).pos
              (identityTensorStateMatrix_posSemidef_of_state (a := A) (path δ))
              (1 / 2 : ℝ)) l
            (nhds (sandwichedRenyiQ
              (State.cqConditioningState E).matrix
              (identityTensorStateMatrix (a := A) σc)
              (State.cqConditioningState E).pos
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σc)
              (1 / 2 : ℝ))) := by
        exact sandwichedRenyiQ_tendsto_of_tendsto_posSemidef
          (by norm_num) (by norm_num) tendsto_const_nhds hreference
          (fun _ => (State.cqConditioningState E).pos)
          (fun δ => identityTensorStateMatrix_posSemidef_of_state
            (a := A) (path δ))
          (State.cqConditioningState E).pos
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σc)
      have hlog_tend :
          Filter.Tendsto
            (fun δ : ℝ => log2 (sandwichedRenyiQ
              (State.cqConditioningState E).matrix
              (identityTensorStateMatrix (a := A) (path δ))
              (State.cqConditioningState E).pos
              (identityTensorStateMatrix_posSemidef_of_state (a := A) (path δ))
              (1 / 2 : ℝ))) l
            (nhds (log2 (sandwichedRenyiQ
              (State.cqConditioningState E).matrix
              (identityTensorStateMatrix (a := A) σc)
              (State.cqConditioningState E).pos
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σc)
              (1 / 2 : ℝ)))) := by
        have hraw := Filter.Tendsto.log hQ_tend hQpos.ne'
        simpa [log2] using
          hraw.div tendsto_const_nhds (ne_of_gt (Real.log_pos one_lt_two))
      have hreal :
          Filter.Tendsto
            (fun δ : ℝ => -(1 / ((1 / 2 : ℝ) - 1)) * log2 (sandwichedRenyiQ
              (State.cqConditioningState E).matrix
              (identityTensorStateMatrix (a := A) (path δ))
              (State.cqConditioningState E).pos
              (identityTensorStateMatrix_posSemidef_of_state (a := A) (path δ))
              (1 / 2 : ℝ))) l
            (nhds (-sandwichedRenyiPSDReferenceLowAlpha
              (State.cqConditioningState E)
              (identityTensorStateMatrix (a := A) σc)
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σc)
              (1 / 2 : ℝ))) := by
        have h := hlog_tend.const_mul (-1 / ((1 / 2 : ℝ) - 1))
        convert h using 1 <;>
          simp [sandwichedRenyiPSDReferenceLowAlpha, div_eq_mul_inv]
      have hcandidate_tend :
          Filter.Tendsto
            (fun δ : ℝ => -sandwichedRenyiPSDReferenceE
              (State.cqConditioningState E)
              (identityTensorStateMatrix (a := A) (path δ))
              (identityTensorStateMatrix_posSemidef_of_state (a := A) (path δ))
              (1 / 2 : ℝ)) l
            (nhds (-sandwichedRenyiPSDReferenceLowAlpha
              (State.cqConditioningState E)
              (identityTensorStateMatrix (a := A) σc)
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σc)
              (1 / 2 : ℝ) : EReal)) := by
        have heq : ∀ᶠ δ in l,
            (fun δ : ℝ => -sandwichedRenyiPSDReferenceE
              (State.cqConditioningState E)
              (identityTensorStateMatrix (a := A) (path δ))
              (identityTensorStateMatrix_posSemidef_of_state (a := A) (path δ))
              (1 / 2 : ℝ)) δ =
            (((-(1 / ((1 / 2 : ℝ) - 1)) * log2 (sandwichedRenyiQ
              (State.cqConditioningState E).matrix
              (identityTensorStateMatrix (a := A) (path δ))
              (State.cqConditioningState E).pos
              (identityTensorStateMatrix_posSemidef_of_state (a := A) (path δ))
              (1 / 2 : ℝ))) : ℝ) : EReal) := by
          filter_upwards [self_mem_nhdsWithin] with δ hδ
          have hpath_pd : (path δ).matrix.PosDef := by
            dsimp [path]
            rw [fullRankApproxMaximallyMixedStatePath,
              fullRankApproxStatePath, dif_pos hδ]
            exact fullRankApproxState_posDef_of_noise σc
              (State.maximallyMixed (B × Y))
              State.maximallyMixed_posDef hδ.1.le hδ.2.le hδ.1
          have hreference_pd :
              (identityTensorStateMatrix (a := A) (path δ)).PosDef :=
            identityTensorStateMatrix_posDef_of_posDef (a := A) (path δ) hpath_pd
          have hQδpos : 0 < sandwichedRenyiQ
              (State.cqConditioningState E).matrix
              (identityTensorStateMatrix (a := A) (path δ))
              (State.cqConditioningState E).pos
              (identityTensorStateMatrix_posSemidef_of_state (a := A) (path δ))
              (1 / 2 : ℝ) :=
            sandwichedRenyiQ_pos_of_state_posDef_reference
              (State.cqConditioningState E) hreference_pd (1 / 2 : ℝ)
          rw [sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one _ _ (by norm_num),
            sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero
              _ _ _ hQδpos.ne']
          rw [← EReal.coe_neg]
          apply EReal.coe_eq_coe_iff.mpr
          simp [sandwichedRenyiPSDReferenceLowAlpha]
        have hreal' := EReal.tendsto_coe.mpr hreal
        exact Filter.Tendsto.congr' (heq.mono fun _ h => h.symm) hreal'
      have hevent : ∀ᶠ δ in l,
          -sandwichedRenyiPSDReferenceE
              (State.cqConditioningState E)
              (identityTensorStateMatrix (a := A) (path δ))
              (identityTensorStateMatrix_posSemidef_of_state (a := A) (path δ))
              (1 / 2 : ℝ) ≤
            (sandwichedUpClassicalFormulaReal E (1 / 2 : ℝ) (by norm_num)
              (by norm_num) : EReal) := by
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        have hF := coordinateYPinchedFullRankPath_posDef σ hδ
        have hcoord : coordinateYPinchedState (path δ) = path δ := by
          dsimp [path]
          rw [fullRankApproxMaximallyMixedStatePath,
            fullRankApproxStatePath, dif_pos hδ]
          exact coordinateYPinchedState_regularized_maximallyMixed_fixed
            σ δ hδ.1.le hδ.2.le
        simpa [hcoord] using
          (sandwichedRenyiPSDReferenceE_arbitrary_reference_le_classicalFormula_half_of_coordinateYPinched_posDef
            E (path δ) hF)
      haveI : Filter.NeBot l := left_nhdsWithin_Ioo_neBot zero_lt_one
      have htarget :
          -sandwichedRenyiPSDReferenceE
              (State.cqConditioningState E)
              (identityTensorStateMatrix (a := A) σc)
              (identityTensorStateMatrix_posSemidef_of_state (a := A) σc)
              (1 / 2 : ℝ) =
            (-sandwichedRenyiPSDReferenceLowAlpha
              (State.cqConditioningState E)
              (identityTensorStateMatrix (a := A) σc)
              (identityTensorStateMatrix_posSemidef_of_state (a := A) σc)
              (1 / 2 : ℝ) : EReal) := by
        rw [sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one _ _ (by norm_num),
          sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero
            _ _ _ hQpos.ne']
      rw [htarget]
      exact le_of_tendsto hcandidate_tend hevent
  exact hpinch.trans hc_le

/-! Every full-rank classical reference ensemble supplies an actual member of
the global source supremum.  This is the lower-bound direction needed when
assembling branchwise source candidates; it keeps the source formula visible
and does not assume that the supremum is attained. -/

theorem sandwichedUpFixedReferenceFormulaReal_le_conditionalSandwichedRenyiUpE
    (E : Ensemble Y (A × B)) (F : Ensemble Y B)
    (hF : (F.cqState.reindex (Equiv.prodComm Y B)).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_pos : 0 < α)
    (hα_ne_one : α ≠ 1) :
    (sandwichedUpFixedReferenceFormulaReal E F α : EReal) ≤
      conditionalSandwichedRenyiUpE E α
        hα_half hα_ne_one := by
  rw [← sandwichedRenyiPSDReferenceE_cq_fullrank_reference_formula
    E F hF α hα_pos hα_ne_one]
  unfold conditionalSandwichedRenyiUpE
  exact le_sSup ⟨F.cqState.reindex (Equiv.prodComm Y B), rfl⟩

/-! The arbitrary-reference upper bound is the `csSup` half of the
source proof.  The endpoint and the two open parameter ranges are kept as
separate cases because the source divergence has different support
conventions at those boundaries. -/

theorem conditionalSandwichedRenyiUpE_le_classicalFormula
    (E : Ensemble Y (A × B)) (α : ℝ) (hα : 1 / 2 ≤ α)
    (hα_ne_one : α ≠ 1) :
    conditionalSandwichedRenyiUpE E α hα hα_ne_one ≤
      (sandwichedUpClassicalFormulaReal E α hα hα_ne_one : EReal) := by
  classical
  letI : Nonempty Y := Ensemble.index_nonempty E
  letI : Nonempty B := by
    rcases (E.states (Classical.choice (inferInstance : Nonempty Y))).nonempty with
      ⟨⟨a, b⟩⟩
    exact ⟨b⟩
  letI : Nonempty A := by
    rcases (E.states (Classical.choice (inferInstance : Nonempty Y))).nonempty with
      ⟨⟨a, b⟩⟩
    exact ⟨a⟩
  unfold conditionalSandwichedRenyiUpE
  refine csSup_le ?_ ?_
  · let σ₀ : State (B × Y) := State.maximallyMixed (B × Y)
    refine ⟨-sandwichedRenyiPSDReferenceE
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A) σ₀)
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ₀) α, ?_⟩
    exact ⟨σ₀, rfl⟩
  · rintro z ⟨σ, rfl⟩
    by_cases hhalf : α = (1 / 2 : ℝ)
    · subst α
      exact sandwichedRenyiPSDReferenceE_arbitrary_reference_le_classicalFormula_half
        E σ
    · have hα_half : 1 / 2 < α := by
        rcases lt_or_eq_of_le hα with h | h
        · exact h
        · exact False.elim (hhalf h.symm)
      rcases lt_or_gt_of_ne hα_ne_one with hα_lt_one | hα_gt_one
      · exact sandwichedRenyiPSDReferenceE_arbitrary_reference_le_classicalFormula_of_half_lt_lt_one
          E σ α hα_half hα_lt_one
      · exact sandwichedRenyiPSDReferenceE_arbitrary_reference_le_classicalFormula_of_one_lt
          E σ α hα_gt_one

/-! A source-shaped optimizer candidate.  The strict positivity hypothesis on
the classical weights is temporary local data for this full-rank candidate;
zero-weight labels are removed by `conditionalRenyiSupport` in the closure
argument. -/

theorem sandwichedUpSourceOptimizerFixedReference_le_conditionalSandwichedRenyiUpE
    (E : Ensemble Y (A × B)) (F : Ensemble Y B)
    (hF : (F.cqState.reindex (Equiv.prodComm Y B)).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_pos : 0 < α)
    (hα_ne_one : α ≠ 1)
    (hEpos : ∀ y, 0 < (E.probs y : ℝ))
    (hbranch : ∀ y,
      sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one =
        sandwichedConditionalBranch E y α hα_half hα_ne_one)
    (hoptimizer : ∀ y,
      (F.probs y : ℝ) =
        sandwichedScalarOptimizerDistribution
          (fun z => (E.probs z : ℝ))
          (fun z => sandwichedConditionalBranch E z α hα_half hα_ne_one)
          α y) :
    (sandwichedUpClassicalFormulaReal E α hα_half hα_ne_one : EReal) ≤
      conditionalSandwichedRenyiUpE E α hα_half hα_ne_one := by
  classical
  letI : Nonempty Y := Ensemble.index_nonempty E
  let p : Y → ℝ := fun y => (E.probs y : ℝ)
  let h : Y → ℝ := fun y =>
    sandwichedConditionalBranch E y α hα_half hα_ne_one
  let r : Y → ℝ := fun y =>
    sandwichedScalarOptimizerWeight (p y) (h y) α
  have hr_pos : ∀ y, 0 < r y := by
    intro y
    dsimp [r, sandwichedScalarOptimizerWeight]
    exact mul_pos (hEpos y) (Real.rpow_pos_of_pos (by norm_num) _)
  have hden_pos : 0 < ∑ y, r y := by
    apply Finset.sum_pos'
    · intro y hy
      exact (hr_pos y).le
    · let y : Y := Classical.choice (inferInstance : Nonempty Y)
      exact ⟨y, Finset.mem_univ y, hr_pos y⟩
  have hscalararg :
      sandwichedScalarPower
          (fun y => (E.probs y : ℝ) *
            Real.rpow 2 (((1 - α) / α) *
              sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one))
          (fun y => (F.probs y : ℝ)) α =
        sandwichedScalarPower r
          (sandwichedScalarOptimizerDistribution p h α) α := by
    unfold sandwichedScalarPower
    apply Finset.sum_congr rfl
    intro y hy
    change
      ((E.probs y : ℝ) *
        Real.rpow 2 (((1 - α) / α) *
          sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one)) ^ α *
        (F.probs y : ℝ) ^ (1 - α) =
      r y ^ α *
        sandwichedScalarOptimizerDistribution p h α y ^ (1 - α)
    rw [hoptimizer y]
    have hr_eq :
        (E.probs y : ℝ) *
            Real.rpow 2 (((1 - α) / α) *
              sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one) =
          r y := by
      simpa [r, p, h, sandwichedScalarOptimizerWeight] using
        congrArg (fun x : ℝ => (E.probs y : ℝ) *
          Real.rpow 2 (((1 - α) / α) * x)) (hbranch y)
    rw [hr_eq]
  have hopt := sandwichedScalarPower_optimizer_weighted p h α hEpos hα_pos
  have hlog_rpow :
      log2 ((∑ y, r y) ^ α) = α * log2 (∑ y, r y) := by
    unfold log2
    rw [Real.log_rpow hden_pos]
    ring
  have hsupport : E.conditionalRenyiSupport = (Finset.univ : Finset Y) := by
    ext y
    rw [Ensemble.mem_conditionalRenyiSupport_iff]
    have hpy : E.probs y ≠ 0 := by
      intro hpy
      have hpy' : (E.probs y : ℝ) = 0 := by simp [hpy]
      linarith [hEpos y]
    simp [hpy]
  have hsource :
      sandwichedUpClassicalFormulaReal E α hα_half hα_ne_one =
        (α / (1 - α)) * log2 (∑ y, r y) := by
    unfold sandwichedUpClassicalFormulaReal
    rw [hsupport]
    congr 2
  have hfixed :
      sandwichedUpFixedReferenceFormulaReal E F α =
        (α / (1 - α)) * log2 (∑ y, r y) := by
    rw [sandwichedUpFixedReferenceFormulaReal_eq_branchFormula
      E F hF α hα_pos hα_ne_one,
      sandwichedUpFixedReferenceBranchFormulaReal_eq_log_scalarPower
        E F hF α hα_pos hα_ne_one]
    rw [hscalararg, hopt, hlog_rpow]
    ring
  have hEq :
      sandwichedUpClassicalFormulaReal E α hα_half hα_ne_one =
        sandwichedUpFixedReferenceFormulaReal E F α := by
    rw [hsource, hfixed]
  rw [hEq]
  exact sandwichedUpFixedReferenceFormulaReal_le_conditionalSandwichedRenyiUpE
    E F hF α hα_half hα_pos hα_ne_one

theorem sandwichedUpFixedReferenceFormulaReal_eq_candidateFormula
    (E : Ensemble Y (A × B)) (F : Ensemble Y B)
    (hF : (F.cqState.reindex (Equiv.prodComm Y B)).matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1)
    (hEpos : ∀ y, 0 < (E.probs y : ℝ)) (c : Y → ℝ)
    (hbranch : ∀ y,
      sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one = c y)
    (hoptimizer : ∀ y,
      (F.probs y : ℝ) = sandwichedScalarOptimizerDistribution
        (fun z => (E.probs z : ℝ)) c α y) :
    sandwichedUpFixedReferenceFormulaReal E F α =
      (α / (1 - α)) * log2 (∑ y, (E.probs y : ℝ) *
        Real.rpow 2 (((1 - α) / α) * c y)) := by
  classical
  letI : Nonempty Y := Ensemble.index_nonempty E
  let p : Y → ℝ := fun y => (E.probs y : ℝ)
  let r : Y → ℝ := fun y =>
    sandwichedScalarOptimizerWeight (p y) (c y) α
  have hr_pos : ∀ y, 0 < r y := by
    intro y
    dsimp [r, sandwichedScalarOptimizerWeight]
    exact mul_pos (hEpos y) (Real.rpow_pos_of_pos (by norm_num) _)
  have hden_pos : 0 < ∑ y, r y := by
    apply Finset.sum_pos'
    · intro y hy
      exact (hr_pos y).le
    · let y : Y := Classical.choice (inferInstance : Nonempty Y)
      exact ⟨y, Finset.mem_univ y, hr_pos y⟩
  have hscalararg :
      sandwichedScalarPower
          (fun y => (E.probs y : ℝ) * Real.rpow 2 (((1 - α) / α) *
            sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one))
          (fun y => (F.probs y : ℝ)) α =
        sandwichedScalarPower r
          (sandwichedScalarOptimizerDistribution p c α) α := by
    unfold sandwichedScalarPower
    apply Finset.sum_congr rfl
    intro y hy
    change
      ((E.probs y : ℝ) * Real.rpow 2 (((1 - α) / α) *
        sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one)) ^ α *
        (F.probs y : ℝ) ^ (1 - α) =
      r y ^ α * sandwichedScalarOptimizerDistribution p c α y ^ (1 - α)
    rw [hoptimizer y]
    have hr_eq :
        (E.probs y : ℝ) * Real.rpow 2 (((1 - α) / α) *
          sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one) = r y := by
      simpa [r, p, sandwichedScalarOptimizerWeight] using
        congrArg (fun x : ℝ => (E.probs y : ℝ) *
          Real.rpow 2 (((1 - α) / α) * x)) (hbranch y)
    rw [hr_eq]
  have hopt := sandwichedScalarPower_optimizer_weighted p c α hEpos hα_pos
  have hlog_rpow : log2 ((∑ y, r y) ^ α) = α * log2 (∑ y, r y) := by
    unfold log2
    rw [Real.log_rpow hden_pos]
    ring
  rw [sandwichedUpFixedReferenceFormulaReal_eq_branchFormula
    E F hF α hα_pos hα_ne_one,
    sandwichedUpFixedReferenceBranchFormulaReal_eq_log_scalarPower
      E F hF α hα_pos hα_ne_one, hscalararg, hopt, hlog_rpow]
  unfold r sandwichedScalarOptimizerWeight
  ring

theorem sandwichedUpFixedReferenceFormulaReal_eq_candidateFormula_nonneg
    (E : Ensemble Y (A × B)) (F : Ensemble Y B)
    (hF : (F.cqState.reindex (Equiv.prodComm Y B)).matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1)
    (hp : ∀ y, 0 ≤ (E.probs y : ℝ))
    (c : Y → ℝ)
    (hden : 0 < ∑ y, sandwichedScalarOptimizerWeight
      (E.probs y : ℝ) (c y) α)
    (hbranch : ∀ y,
      sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one = c y)
    (hoptimizer : ∀ y,
      (F.probs y : ℝ) = sandwichedScalarOptimizerDistribution
        (fun z => (E.probs z : ℝ)) c α y) :
    sandwichedUpFixedReferenceFormulaReal E F α =
      (α / (1 - α)) * log2 (∑ y, (E.probs y : ℝ) *
        Real.rpow 2 (((1 - α) / α) * c y)) := by
  classical
  letI : Nonempty Y := Ensemble.index_nonempty E
  let p : Y → ℝ := fun y => (E.probs y : ℝ)
  let r : Y → ℝ := fun y =>
    sandwichedScalarOptimizerWeight (p y) (c y) α
  have hr_nonneg : ∀ y, 0 ≤ r y := by
    intro y
    dsimp [r, sandwichedScalarOptimizerWeight]
    exact mul_nonneg (hp y) (Real.rpow_pos_of_pos (by norm_num) _).le
  have hscalararg :
      sandwichedScalarPower
          (fun y => (E.probs y : ℝ) * Real.rpow 2 (((1 - α) / α) *
            sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one))
          (fun y => (F.probs y : ℝ)) α =
        sandwichedScalarPower r
          (sandwichedScalarOptimizerDistribution p c α) α := by
    unfold sandwichedScalarPower
    apply Finset.sum_congr rfl
    intro y hy
    change
      ((E.probs y : ℝ) * Real.rpow 2 (((1 - α) / α) *
        sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one)) ^ α *
        (F.probs y : ℝ) ^ (1 - α) =
      r y ^ α * sandwichedScalarOptimizerDistribution p c α y ^ (1 - α)
    rw [hoptimizer y]
    have hr_eq :
        (E.probs y : ℝ) * Real.rpow 2 (((1 - α) / α) *
          sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one) =
        r y := by
      simpa [r, p, sandwichedScalarOptimizerWeight] using
        congrArg (fun x : ℝ => (E.probs y : ℝ) *
          Real.rpow 2 (((1 - α) / α) * x)) (hbranch y)
    rw [hr_eq]
  have hopt := sandwichedScalarPower_optimizer_of_nonneg r α hr_nonneg hden hα_pos
  have hdist : sandwichedScalarOptimizerDistribution p c α =
      (fun y => r y / ∑ z, r z) := by
    funext y
    rfl
  have hlog_rpow : log2 ((∑ y, r y) ^ α) = α * log2 (∑ y, r y) := by
    unfold log2
    rw [Real.log_rpow hden]
    ring
  rw [sandwichedUpFixedReferenceFormulaReal_eq_branchFormula
    E F hF α hα_pos hα_ne_one,
    sandwichedUpFixedReferenceBranchFormulaReal_eq_log_scalarPower
      E F hF α hα_pos hα_ne_one, hscalararg, hdist, hopt, hlog_rpow]
  unfold r sandwichedScalarOptimizerWeight
  ring

/-! Zero-probability labels are made harmless before taking a full-rank
reference limit.  The optimizer is mixed with the uniform distribution, while
labels outside the source support receive the maximally mixed side state. -/

omit [DecidableEq Y] in
theorem sandwichedSourceOptimizerRegularizedEnsemble
    [Nonempty B] [Nonempty Y]
    (E : Ensemble Y (A × B)) (α : ℝ) (_hα_pos : 0 < α)
    (h : Y → ℝ) (s : Y → State B) (δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hden : 0 < ∑ y,
      sandwichedScalarOptimizerWeight (E.probs y : ℝ) (h y) α) :
    ∃ F : Ensemble Y B,
      (∀ y, 0 < F.probs y) ∧
      (∀ y,
        (F.probs y : ℝ) =
          (1 - δ) * sandwichedScalarOptimizerDistribution
              (fun z => (E.probs z : ℝ)) h α y +
            δ / (Fintype.card Y : ℝ)) ∧
      (∀ y, E.probs y ≠ 0 → F.states y = s y) ∧
      (∀ y, E.probs y = 0 → F.states y = State.maximallyMixed B) := by
  classical
  let p : Y → ℝ := fun y => (E.probs y : ℝ)
  let q : Y → ℝ := sandwichedScalarOptimizerDistribution p h α
  let qδ : Y → ℝ := fun y => (1 - δ) * q y + δ / (Fintype.card Y : ℝ)
  have hp : ∀ y, 0 ≤ p y := by
    intro y
    exact_mod_cast E.prob_nonneg y
  have hq_nonneg : ∀ y, 0 ≤ q y := by
    intro y
    exact sandwichedScalarOptimizerDistribution_nonneg p h α hp y
  have hq_sum : ∑ y, q y = 1 := by
    dsimp [q]
    exact sandwichedScalarOptimizerDistribution_sum_one p h α
      (ne_of_gt hden)
  have hcard_pos : 0 < (Fintype.card Y : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty Y)
  have hqδ_pos : ∀ y, 0 < qδ y := by
    intro y
    dsimp [qδ]
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr hδ_lt_one.le) (hq_nonneg y))
      (div_pos hδ_pos hcard_pos)
  have hqδ_sum : ∑ y, qδ y = 1 := by
    dsimp [qδ]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hq_sum]
    rw [← Finset.sum_div, Finset.sum_const, Finset.card_univ]
    field_simp [hcard_pos.ne']
    ring
  let states : Y → State B := fun y =>
    if E.probs y = 0 then State.maximallyMixed B else s y
  let F : Ensemble Y B :=
    { probs := fun y => ⟨qδ y, (hqδ_pos y).le⟩
      weights_sum := by
        apply NNReal.eq
        simpa using hqδ_sum
      states := states }
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro y
    exact NNReal.coe_pos.mpr (hqδ_pos y)
  · intro y
    rfl
  · intro y hnonzero
    simp [F, states, hnonzero]
  · intro y hzero
    simp [F, states, hzero]

/-! Finite support choices can approach the sum of branch suprema without
assuming that any branch supremum is attained. -/

theorem finiteSelectionSumSet_exists_lt_sSup_additive
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (S : ι → Set ℝ)
    (hs : s.Nonempty) (hne : ∀ i ∈ s, (S i).Nonempty)
    (hbd : ∀ i ∈ s, BddAbove (S i)) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ι → ℝ,
      (∀ i ∈ s, f i ∈ S i) ∧
        sSup (finiteSelectionSumSet s S) - ε < ∑ i ∈ s, f i := by
  classical
  let n : ℝ := (s.card : ℝ)
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (Finset.card_pos.mpr hs)
  have hεn : 0 < ε / n := div_pos hε hn
  have hex : ∀ i ∈ s, ∃ x ∈ S i,
      sSup (S i) - ε / n < x := by
    intro i hi
    apply (lt_csSup_iff (hbd i hi) (hne i hi)).mp
    linarith
  choose f hfmem hflt using hex
  let g : ι → ℝ := fun i => if hi : i ∈ s then f i hi else 0
  have hgmem : ∀ i ∈ s, g i ∈ S i := by
    intro i hi
    simp [g, hi, hfmem i hi]
  refine ⟨g, hgmem, ?_⟩
  have hsum_lt :
      (∑ i ∈ s, (sSup (S i) - ε / n)) < ∑ i ∈ s, g i := by
    apply Finset.sum_lt_sum_of_nonempty hs
    intro i hi
    simpa [g, hi] using hflt i hi
  calc
    sSup (finiteSelectionSumSet s S) - ε =
        (∑ i ∈ s, sSup (S i)) - ε := by
      rw [finiteSelectionSumSet_sSup s S hne hbd]
    _ = ∑ i ∈ s, (sSup (S i) - ε / n) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const]
      simp [n, nsmul_eq_mul]
      field_simp [hn.ne']
    _ < ∑ i ∈ s, g i := hsum_lt

/-! A finite family of branch suprema can be approached from below after
the source scalar transform.  This is the numerical part of the source
argument; it deliberately uses neighbourhoods rather than an assumed
maximizer. -/

theorem finiteSourceLogRpow_approximation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Set ℝ) (p : ι → ℝ) (α : ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hS_nonempty : ∀ i, (S i).Nonempty)
    (hS_bdd : ∀ i, BddAbove (S i))
    (_hα_pos : 0 < α) (_hα_ne_one : α ≠ 1) :
    ∀ ε > 0, ∃ c : ι → ℝ,
      (∀ i, c i ∈ S i) ∧
      (α / (1 - α)) * log2
          (∑ i, p i * Real.rpow 2 (((1 - α) / α) * c i)) >
        (α / (1 - α)) * log2
          (∑ i, p i * Real.rpow 2 (((1 - α) / α) * sSup (S i))) - ε := by
  intro ε hε
  let k : ℝ := (1 - α) / α
  let a : ℝ := α / (1 - α)
  let h : ι → ℝ := fun i => sSup (S i)
  let G : (ι → ℝ) → ℝ := fun x =>
    a * log2 (∑ i, p i * Real.rpow 2 (k * x i))
  have hp_exists : ∃ i, 0 < p i := by
    by_contra h
    push Not at h
    have hp_zero : ∀ i, p i = 0 := by
      intro i
      exact le_antisymm (h i) (hp_nonneg i)
    simp [hp_zero] at hp_sum
  obtain ⟨i₀, hi₀⟩ := hp_exists
  have hsum_pos : 0 < ∑ i, p i * Real.rpow 2 (k * h i) := by
    apply Finset.sum_pos'
    · intro i hi
      exact mul_nonneg (hp_nonneg i) (Real.rpow_nonneg (by norm_num) _)
    · exact ⟨i₀, Finset.mem_univ i₀, by
        exact mul_pos hi₀ (Real.rpow_pos_of_pos (by norm_num) _)
      ⟩
  have hpow_cont : ∀ i, Continuous (fun x : ι → ℝ => Real.rpow 2 (k * x i)) := by
    intro i
    exact (Real.continuous_const_rpow (a := (2 : ℝ)) (by norm_num)).comp
      (continuous_const.mul (continuous_apply i))
  have hsum_cont : Continuous (fun x : ι → ℝ =>
      ∑ i, p i * Real.rpow 2 (k * x i)) := by
    fun_prop
  have hG_cont : ContinuousAt G h := by
    dsimp [G]
    unfold log2
    change Filter.Tendsto (fun x : ι → ℝ =>
        a * (Real.log (∑ i, p i * Real.rpow 2 (k * x i)) /
          Real.log 2)) (nhds h)
      (nhds (a * (Real.log (∑ i, p i * Real.rpow 2 (k * h i)) /
        Real.log 2)))
    have hlog : Filter.Tendsto (fun z : ℝ => a * (Real.log z / Real.log 2))
        (nhds (∑ i, p i * Real.rpow 2 (k * h i)))
        (nhds (a * (Real.log (∑ i, p i * Real.rpow 2 (k * h i)) /
          Real.log 2))) :=
      ((Real.continuousAt_log hsum_pos.ne').div_const _ |>.const_mul a)
    exact hlog.comp hsum_cont.continuousAt
  have hG_event : ∀ᶠ x in nhds h, G h - ε < G x := by
    have htarget : G h - ε < G h := by linarith
    exact hG_cont.eventually (lt_mem_nhds htarget)
  rcases Metric.mem_nhds_iff.mp hG_event with ⟨δ, hδ, hδ_subset⟩
  have hδ_half : 0 < δ / 2 := by linarith
  have hchoice : ∀ i, ∃ x ∈ S i, h i - δ / 2 < x := by
    intro i
    apply (lt_csSup_iff (hS_bdd i) (hS_nonempty i)).mp
    linarith
  choose c hc_mem hc_close using hchoice
  have hle_sup : ∀ i, c i ≤ h i := by
    intro i
    exact le_csSup (hS_bdd i) (hc_mem i)
  have hdist : dist c h < δ := by
    rw [dist_pi_lt_iff hδ]
    intro i
    rw [Real.dist_eq]
    rw [abs_lt]
    constructor <;> linarith [hc_close i, hle_sup i]
  refine ⟨c, hc_mem, ?_⟩
  exact hδ_subset (Metric.mem_ball'.mpr (by simpa [dist_comm] using hdist))

theorem conditionalSandwichedRenyiUp_classicalConditioning_of_ne_half_of_positive
    (E : Ensemble Y (A × B)) (α : ℝ) (hα : 1 / 2 ≤ α)
    (hα_ne_one : α ≠ 1) (hα_ne_half : α ≠ (1 / 2 : ℝ))
    (hEpos : ∀ y, 0 < (E.probs y : ℝ)) :
    conditionalSandwichedRenyiUpE E α hα hα_ne_one =
      (sandwichedUpClassicalFormulaReal E α hα hα_ne_one : EReal) := by
  classical
  letI : Nonempty Y := Ensemble.index_nonempty E
  letI : Nonempty B := by
    rcases (E.states (Classical.choice (inferInstance : Nonempty Y))).nonempty with
      ⟨⟨a, b⟩⟩
    exact ⟨b⟩
  have hα_pos : 0 < α := lt_of_lt_of_le (by norm_num) hα
  let S : Y → Set ℝ := fun y =>
    (E.states y).conditionalSandwichedRenyiUpSourceValueSet α hα_pos hα_ne_one
  have hS_nonempty : ∀ y, (S y).Nonempty := by
    intro y
    exact (E.states y).conditionalSandwichedRenyiUpSourceValueSet_nonempty
      α hα_pos hα_ne_one
  have hS_bdd : ∀ y, BddAbove (S y) := by
    intro y
    rcases lt_or_gt_of_ne hα_ne_one with hα_lt | hα_gt
    · have hhalf : 1 / 2 < α := by
        rcases lt_or_eq_of_le hα with h | h
        · exact h
        · exact False.elim (hα_ne_half h.symm)
      exact (E.states y).conditionalSandwichedRenyiUpSourceValueSet_bddAbove_of_half_lt_lt_one
        hhalf hα_lt
    · exact (E.states y).conditionalSandwichedRenyiUpSourceValueSet_bddAbove_of_one_lt hα_gt
  have hbranch_sup : ∀ y,
      sandwichedConditionalBranch E y α hα hα_ne_one = sSup (S y) := by
    intro y
    have hα_ne_half' : α ≠ (2 : ℝ)⁻¹ := by
      simpa [one_div] using hα_ne_half
    rw [sandwichedConditionalBranch_eq_source_of_ne_half
      E y α hα hα_ne_one hα_ne_half']
    rfl
  let p : Y → ℝ := fun y => (E.probs y : ℝ)
  have hp_nonneg : ∀ y, 0 ≤ p y := by
    intro y
    exact (hEpos y).le
  have hp_sum : ∑ y, p y = 1 := by
    dsimp [p]
    exact_mod_cast E.weights_sum
  have hupper : conditionalSandwichedRenyiUpE E α hα hα_ne_one ≤
      (sandwichedUpClassicalFormulaReal E α hα hα_ne_one : EReal) :=
    conditionalSandwichedRenyiUpE_le_classicalFormula E α hα hα_ne_one
  apply le_antisymm hupper
  unfold conditionalSandwichedRenyiUpE
  have hs_eq : sSup {h : EReal |
      ∃ σ : State (B × Y), h = -sandwichedRenyiPSDReferenceE
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ) α} =
      (sandwichedUpClassicalFormulaReal E α hα hα_ne_one : EReal) := by
    apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    · let σ₀ : State (B × Y) := State.maximallyMixed (B × Y)
      exact ⟨-sandwichedRenyiPSDReferenceE
          (State.cqConditioningState E)
          (identityTensorStateMatrix (a := A) σ₀)
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σ₀) α,
        σ₀, rfl⟩
    · intro z hz
      rcases hz with ⟨σ, rfl⟩
      rcases lt_or_eq_of_le hα with hhalf | hhalf
      · rcases lt_or_gt_of_ne hα_ne_one with hlt | hgt
        · exact sandwichedRenyiPSDReferenceE_arbitrary_reference_le_classicalFormula_of_half_lt_lt_one
            E σ α hhalf hlt
        · exact sandwichedRenyiPSDReferenceE_arbitrary_reference_le_classicalFormula_of_one_lt
            E σ α hgt
      · exact False.elim (hα_ne_half hhalf.symm)
    · intro r hr
      rcases EReal.lt_iff_exists_real_btwn.mp hr with ⟨x, hxr, hxf⟩
      let formula : ℝ := sandwichedUpClassicalFormulaReal E α hα hα_ne_one
      have hxf' : x < formula := EReal.coe_lt_coe_iff.mp hxf
      have hε : 0 < formula - x := by linarith
      obtain ⟨c, hc_mem, hc_formula⟩ := finiteSourceLogRpow_approximation
        S p α hp_nonneg hp_sum hS_nonempty hS_bdd hα_pos hα_ne_one
        (formula - x) hε
      have hc_formula' : x < (α / (1 - α)) * log2
          (∑ y, (E.probs y : ℝ) * Real.rpow 2 (((1 - α) / α) * c y)) := by
        have hsupport : E.conditionalRenyiSupport = (Finset.univ : Finset Y) := by
          ext y
          rw [E.mem_conditionalRenyiSupport_iff]
          constructor
          · intro _
            simp
          · intro _ hz
            apply (hEpos y).ne'
            simp [hz]
        have htarget : formula =
            (α / (1 - α)) * log2
              (∑ y, (E.probs y : ℝ) * Real.rpow 2
                (((1 - α) / α) * sSup (S y))) := by
          unfold formula sandwichedUpClassicalFormulaReal
          rw [hsupport]
          apply congrArg (fun z : ℝ => (α / (1 - α)) * log2 z)
          apply Finset.sum_congr rfl
          intro y hy
          rw [← hbranch_sup y]
        have hc_formula0 :
            (α / (1 - α)) * log2 (∑ y, (E.probs y : ℝ) *
              Real.rpow 2 (((1 - α) / α) * sSup (S y))) - (formula - x) <
            (α / (1 - α)) * log2 (∑ y, (E.probs y : ℝ) *
              Real.rpow 2 (((1 - α) / α) * c y)) := by
          simpa [p] using hc_formula
        rw [← htarget] at hc_formula0
        linarith
      choose s hs hsc using hc_mem
      let q : Y → ℝ := sandwichedScalarOptimizerDistribution p c α
      have hweight : ∀ y, 0 < sandwichedScalarOptimizerWeight (p y) (c y) α := by
        intro y
        exact mul_pos (hEpos y) (Real.rpow_pos_of_pos (by norm_num) _)
      have hden : 0 < ∑ y, sandwichedScalarOptimizerWeight (p y) (c y) α := by
        apply Finset.sum_pos'
        · intro y hy
          exact (hweight y).le
        · let y : Y := Classical.choice (inferInstance : Nonempty Y)
          exact ⟨y, Finset.mem_univ y, hweight y⟩
      have hqpos : ∀ y, 0 < q y := by
        intro y
        dsimp [q]
        exact div_pos (hweight y) hden
      have hqsum : ∑ y, q y = 1 := by
        dsimp [q]
        exact sandwichedScalarOptimizerDistribution_sum_one p c α hden.ne'
      let F : Ensemble Y B :=
        { probs := fun y => ⟨q y, (hqpos y).le⟩
          weights_sum := by
            apply NNReal.eq
            simpa using hqsum
          states := s }
      have hF : (F.cqState.reindex (Equiv.prodComm Y B)).matrix.PosDef := by
        apply sandwiched_reference_cq_posDef_of_positive F
        · intro y
          exact_mod_cast hqpos y
        · exact hs
      have hbranch : ∀ y,
            sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one = c y := by
        intro y
        simpa [sandwichedFixedReferenceBranchValue] using (hsc y).symm
      have hoptimizer : ∀ y, (F.probs y : ℝ) = q y := by
        intro y
        rfl
      have hfixed := sandwichedUpFixedReferenceFormulaReal_eq_candidateFormula
        E F hF α hα_pos hα_ne_one hEpos c hbranch hoptimizer
      have hcandidate := sandwichedUpFixedReferenceFormulaReal_le_conditionalSandwichedRenyiUpE
        E F hF α hα hα_pos hα_ne_one
      have hvalue := sandwichedRenyiPSDReferenceE_cq_fullrank_reference_formula
        E F hF α hα_pos hα_ne_one
      refine ⟨-sandwichedRenyiPSDReferenceE
          (State.cqConditioningState E)
          (identityTensorStateMatrix (a := A)
            (F.cqState.reindex (Equiv.prodComm Y B)))
          (identityTensorStateMatrix_posSemidef_of_state
            (a := A) (F.cqState.reindex (Equiv.prodComm Y B))) α,
        ⟨F.cqState.reindex (Equiv.prodComm Y B), rfl⟩, ?_⟩
      rw [hvalue, hfixed]
      exact hxr.trans (EReal.coe_lt_coe_iff.mpr hc_formula')
  exact hs_eq.symm.le

theorem conditionalSandwichedRenyiUp_classicalConditioning_exact
    (E : Ensemble Y (A × B)) (α : ℝ) (hα : 1 / 2 ≤ α)
    (hα_ne_one : α ≠ 1) :
    conditionalSandwichedRenyiUpE E α hα hα_ne_one =
      (sandwichedUpClassicalFormulaReal E α hα hα_ne_one : EReal) := by
  classical
  letI : Nonempty Y := Ensemble.index_nonempty E
  letI : Nonempty B := by
    rcases (E.states (Classical.choice (inferInstance : Nonempty Y))).nonempty with
      ⟨⟨a, b⟩⟩
    exact ⟨b⟩
  letI : Nonempty A := by
    rcases (E.states (Classical.choice (inferInstance : Nonempty Y))).nonempty with
      ⟨⟨a, b⟩⟩
    exact ⟨a⟩
  have hα_pos : 0 < α := lt_of_lt_of_le (by norm_num) hα
  let S : Y → Set ℝ := fun y =>
    (E.states y).conditionalSandwichedRenyiUpSourceValueSet α hα_pos hα_ne_one
  have hS_nonempty : ∀ y, (S y).Nonempty := by
    intro y
    exact (E.states y).conditionalSandwichedRenyiUpSourceValueSet_nonempty
      α hα_pos hα_ne_one
  have hS_bdd : ∀ y, BddAbove (S y) := by
    intro y
    by_cases hh : α = (1 / 2 : ℝ)
    · subst α
      refine ⟨(E.states y).conditionalMaxEntropy, ?_⟩
      intro x hx
      rcases hx with ⟨σ, hσ, rfl⟩
      rw [sandwichedUpSourceCandidate_half_eq_conditionalMaxEntropyCandidate
        (E.states y) σ hσ]
      exact le_csSup
        ((E.states y).conditionalMaxEntropyValueSet_bddAbove (a := A))
        ⟨σ, conditionalMaxEntropyExponentCandidate_pos_of_posDef
          (E.states y) σ hσ, rfl⟩
    · rcases lt_or_gt_of_ne hα_ne_one with hlt | hgt
      · have hhalf : 1 / 2 < α := lt_of_le_of_ne hα (Ne.symm hh)
        exact (E.states y).conditionalSandwichedRenyiUpSourceValueSet_bddAbove_of_half_lt_lt_one
          hhalf hlt
      · exact (E.states y).conditionalSandwichedRenyiUpSourceValueSet_bddAbove_of_one_lt hgt
  have hbranch_sup : ∀ y,
      sandwichedConditionalBranch E y α hα hα_ne_one = sSup (S y) := by
    intro y
    by_cases hh : α = (1 / 2 : ℝ)
    · subst α
      unfold sandwichedConditionalBranch
      norm_num [conditionalSandwichedRenyiUpFiniteOrder]
      convert (conditionalSandwichedRenyiUpSource_half_eq_conditionalMaxEntropy
          (E.states y)).symm using 1
    · have hne : α ≠ (2 : ℝ)⁻¹ := by simpa [one_div] using hh
      rw [sandwichedConditionalBranch_eq_source_of_ne_half
        E y α hα hα_ne_one hne]
      rfl
  have hp : ∀ y, 0 ≤ (E.probs y : ℝ) := fun y => E.prob_nonneg y
  have hp_sum : ∑ y, (E.probs y : ℝ) = 1 := by
    exact_mod_cast E.weights_sum
  have hupper := conditionalSandwichedRenyiUpE_le_classicalFormula E α hα hα_ne_one
  apply le_antisymm hupper
  unfold conditionalSandwichedRenyiUpE
  refine (show sSup {h : EReal |
      ∃ σ : State (B × Y), h = -sandwichedRenyiPSDReferenceE
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef_of_state
          (a := A) σ) α} =
      (sandwichedUpClassicalFormulaReal E α hα hα_ne_one : EReal) from ?_).symm.le
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · let σ₀ : State (B × Y) := State.maximallyMixed (B × Y)
    exact ⟨-sandwichedRenyiPSDReferenceE
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A) σ₀)
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ₀) α,
      σ₀, rfl⟩
  · intro z hz
    rcases hz with ⟨σ, rfl⟩
    by_cases hh : α = (1 / 2 : ℝ)
    · subst α
      exact sandwichedRenyiPSDReferenceE_arbitrary_reference_le_classicalFormula_half
        E σ
    · rcases lt_or_gt_of_ne hα_ne_one with hlt | hgt
      · have hhalf : 1 / 2 < α := lt_of_le_of_ne hα (Ne.symm hh)
        exact sandwichedRenyiPSDReferenceE_arbitrary_reference_le_classicalFormula_of_half_lt_lt_one
          E σ α hhalf hlt
      · exact sandwichedRenyiPSDReferenceE_arbitrary_reference_le_classicalFormula_of_one_lt
          E σ α hgt
  · intro r hr
    rcases EReal.lt_iff_exists_real_btwn.mp hr with ⟨x, hxr, hxf⟩
    let formula : ℝ := sandwichedUpClassicalFormulaReal E α hα hα_ne_one
    have hxf' : x < formula := EReal.coe_lt_coe_iff.mp hxf
    have hε : 0 < formula - x := by linarith
    obtain ⟨c, hc_mem, hc_formula⟩ := finiteSourceLogRpow_approximation
      S (fun y => (E.probs y : ℝ)) α hp hp_sum hS_nonempty hS_bdd
      hα_pos hα_ne_one (formula - x) hε
    have hsum_support (f : Y → ℝ)
        (hf : ∀ y, E.probs y = 0 → f y = 0) :
        ∑ y ∈ E.conditionalRenyiSupport, f y = ∑ y, f y := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y hy hnot
      exact hf y ((E.not_mem_conditionalRenyiSupport_iff y).mp hnot)
    have htarget : formula =
        (α / (1 - α)) * log2
          (∑ y, (E.probs y : ℝ) * Real.rpow 2
            (((1 - α) / α) * sSup (S y))) := by
      unfold formula sandwichedUpClassicalFormulaReal
      rw [hsum_support]
      · apply congrArg (fun z : ℝ => (α / (1 - α)) * log2 z)
        apply Finset.sum_congr rfl
        intro y hy
        rw [← hbranch_sup y]
      · intro y hzero
        simp [hzero]
    have hc_formula' : x < (α / (1 - α)) * log2
        (∑ y, (E.probs y : ℝ) * Real.rpow 2
          (((1 - α) / α) * c y)) := by
      have hc0 :
          (α / (1 - α)) * log2
              (∑ y, (E.probs y : ℝ) * Real.rpow 2
                (((1 - α) / α) * sSup (S y))) - (formula - x) <
            (α / (1 - α)) * log2
              (∑ y, (E.probs y : ℝ) * Real.rpow 2
                (((1 - α) / α) * c y)) := by
        simpa using hc_formula
      rw [← htarget] at hc0
      linarith
    choose s hs hsc using hc_mem
    let p : Y → ℝ := fun y => (E.probs y : ℝ)
    let h : Y → ℝ := fun y => c y
    let rweight : Y → ℝ := fun y =>
      sandwichedScalarOptimizerWeight (p y) (h y) α
    have hr_nonneg : ∀ y, 0 ≤ rweight y := by
      intro y
      dsimp [rweight, sandwichedScalarOptimizerWeight]
      exact mul_nonneg (hp y) (Real.rpow_pos_of_pos (by norm_num) _).le
    have hp_exists : ∃ y, 0 < p y := by
      by_contra hn
      push Not at hn
      have hz : ∀ y, p y = 0 := fun y => le_antisymm (hn y) (hp y)
      have hsum0 : ∑ y, p y = 0 := by simp [hz]
      linarith [hp_sum, hsum0]
    obtain ⟨y₀, hy₀⟩ := hp_exists
    have hden : 0 < ∑ y, rweight y := by
      apply Finset.sum_pos'
      · intro y hy
        exact (hr_nonneg y)
      · exact ⟨y₀, Finset.mem_univ y₀,
          mul_pos hy₀ (Real.rpow_pos_of_pos (by norm_num) _)
        ⟩
    let q : Y → ℝ := sandwichedScalarOptimizerDistribution p h α
    have hqzero : ∀ y, rweight y = 0 → q y = 0 := by
      intro y hry
      dsimp [q, sandwichedScalarOptimizerDistribution]
      change rweight y / ∑ z, rweight z = 0
      rw [hry]
      simp
    have hqpos : ∀ y, rweight y ≠ 0 → 0 < q y := by
      intro y hry
      dsimp [q, sandwichedScalarOptimizerDistribution]
      exact div_pos (lt_of_le_of_ne (hr_nonneg y) (Ne.symm hry)) hden
    have hscalar := sandwichedScalarPower_uniformMix_tendsto
      rweight q α hα_pos hqzero hqpos
    have hscalar_pos : 0 < sandwichedScalarPower rweight q α := by
      rw [show q = (fun y => rweight y / ∑ z, rweight z) by
        funext y; rfl]
      rw [sandwichedScalarPower_optimizer_of_nonneg rweight α hr_nonneg hden hα_pos]
      exact Real.rpow_pos_of_pos hden _
    have hH : Filter.Tendsto
        (fun δ : ℝ => (1 / (1 - α)) * log2
          (sandwichedScalarPower rweight
            (fun y => (1 - δ) * q y + δ / (Fintype.card Y : ℝ)) α))
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 1))
        (nhds ((α / (1 - α)) * log2 (∑ y, rweight y))) := by
      have hlog := (Real.continuousAt_log hscalar_pos.ne').tendsto.comp hscalar
      have hlog2 : Filter.Tendsto
          (fun δ : ℝ => log2 (sandwichedScalarPower rweight
            (fun y => (1 - δ) * q y + δ / (Fintype.card Y : ℝ)) α))
          (nhdsWithin (0 : ℝ) (Set.Ioo 0 1))
          (nhds (α * log2 (∑ y, rweight y))) := by
        unfold log2
        have hqdef : q = (fun y => rweight y / ∑ z, rweight z) := by
          funext y
          rfl
        rw [hqdef]
        have hlog' := hlog.div_const (Real.log 2)
        rw [hqdef] at hlog'
        rw [sandwichedScalarPower_optimizer_of_nonneg rweight α hr_nonneg hden hα_pos]
          at hlog'
        convert hlog' using 1
        apply congrArg nhds
        rw [Real.log_rpow hden]
        ring
      have := hlog2.const_mul (1 / (1 - α))
      convert this using 1
      all_goals ring
    have htargetH : x < (α / (1 - α)) * log2 (∑ y, rweight y) := by
      unfold rweight sandwichedScalarOptimizerWeight p h
      exact hc_formula'
    have hmem : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioo 0 1),
        x < (1 / (1 - α)) * log2
          (sandwichedScalarPower rweight
            (fun y => (1 - δ) * q y + δ / (Fintype.card Y : ℝ)) α) :=
      hH.eventually (Ioi_mem_nhds htargetH)
    have hmemclosure : (0 : ℝ) ∈ closure (Set.Ioo 0 1) := by
      rw [closure_Ioo (by norm_num)]
      exact ⟨le_rfl, by norm_num⟩
    letI : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) := by
      exact mem_closure_iff_nhdsWithin_neBot.mp hmemclosure
    obtain ⟨δ, hδval, hδmem⟩ := (hmem.and self_mem_nhdsWithin).exists
    have hδpos : 0 < δ := hδmem.1
    have hδlt : δ < 1 := hδmem.2
    obtain ⟨F, hFprob, hFq, hFstate, hFzero⟩ := sandwichedSourceOptimizerRegularizedEnsemble
      E α hα_pos h s δ hδpos hδlt hden
    have hF : (F.cqState.reindex (Equiv.prodComm Y B)).matrix.PosDef := by
      apply sandwiched_reference_cq_posDef_of_positive F
      · exact hFprob
      · intro y
        by_cases hp0 : E.probs y = 0
        · simpa [hFzero y hp0] using State.maximallyMixed_posDef (a := B)
        · simpa [hFstate y hp0] using hs y
    have hbranch_pos : ∀ y, E.probs y ≠ 0 →
        sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one = c y := by
      intro y hp0
      simpa [sandwichedFixedReferenceBranchValue, hFstate y hp0] using (hsc y).symm
    have hfixed : sandwichedUpFixedReferenceFormulaReal E F α =
        (1 / (1 - α)) * log2
          (sandwichedScalarPower rweight
            (fun y => (1 - δ) * q y + δ / (Fintype.card Y : ℝ)) α) := by
      rw [sandwichedUpFixedReferenceFormulaReal_eq_branchFormula
        E F hF α hα_pos hα_ne_one,
        sandwichedUpFixedReferenceBranchFormulaReal_eq_log_scalarPower
          E F hF α hα_pos hα_ne_one]
      congr 2
      unfold sandwichedScalarPower
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hp0 : E.probs y = 0
      · simp [rweight, p, sandwichedScalarOptimizerWeight, hp0,
          Real.zero_rpow hα_pos.ne']
      · change
          ((E.probs y : ℝ) * Real.rpow 2 (((1 - α) / α) *
            sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one)) ^ α *
            (F.probs y : ℝ) ^ (1 - α) =
          rweight y ^ α *
            ((1 - δ) * q y + δ / (Fintype.card Y : ℝ)) ^ (1 - α)
        rw [hFq y, hbranch_pos y hp0]
        rfl
    have hvalue := sandwichedRenyiPSDReferenceE_cq_fullrank_reference_formula
      E F hF α hα_pos hα_ne_one
    refine ⟨-sandwichedRenyiPSDReferenceE
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A)
          (F.cqState.reindex (Equiv.prodComm Y B)))
        (identityTensorStateMatrix_posSemidef_of_state
          (a := A) (F.cqState.reindex (Equiv.prodComm Y B))) α,
      ⟨F.cqState.reindex (Equiv.prodComm Y B), rfl⟩, ?_⟩
    rw [hvalue, hfixed]
    exact hxr.trans (EReal.coe_lt_coe_iff.mpr hδval)

/-- The sandwiched up-arrow conditional entropy under a classical `Y`. -/
theorem conditionalSandwichedRenyiUp_classicalConditioning
    (E : Ensemble Y (A × B)) (α : ℝ) (hα : 1 / 2 ≤ α)
    (hα_ne_one : α ≠ 1) (σ : State (B × Y)) :
    -sandwichedRenyiPSDReferenceE
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef_of_state
          (a := A) σ) α ≤
      conditionalSandwichedRenyiUpE E α hα hα_ne_one := by
  unfold conditionalSandwichedRenyiUpE
  exact le_sSup ⟨σ, rfl⟩


end State

end

end QIT
