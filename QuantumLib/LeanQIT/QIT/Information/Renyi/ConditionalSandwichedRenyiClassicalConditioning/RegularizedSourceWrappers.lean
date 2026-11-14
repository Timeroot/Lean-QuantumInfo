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

/-!
# public source-shaped wrappers (regularized route)

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

/-! ### Source-facing declarations -/

/-! The branch quantity below is the normalized source optimizer for the
conditional state at a fixed classical label.  Keeping it as a separate
definition makes the scalar optimizer formula readable and leaves the zero
probability labels outside every logarithm. -/

noncomputable def sandwichedConditionalBranch
    (E : Ensemble Y (A × B)) (y : Y) (α : ℝ)
    (_hα : 1 / 2 ≤ α) (_hα_ne_one : α ≠ 1) : ℝ :=
  (E.states y).conditionalSandwichedRenyiUpFiniteOrder α

omit [DecidableEq Y] in
theorem sandwichedConditionalBranch_eq_source_of_ne_half
    (E : Ensemble Y (A × B)) (y : Y) (α : ℝ)
    (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1)
    (hα_ne_half : α ≠ (2 : ℝ)⁻¹) :
    sandwichedConditionalBranch E y α hα hα_ne_one =
      (E.states y).conditionalSandwichedRenyiUpSource α
        (by linarith) hα_ne_one := by
  unfold sandwichedConditionalBranch
  exact conditionalSandwichedRenyiUpFiniteOrder_of_pos_ne_one_ne_half
    (E.states y) (by linarith) hα_ne_one hα_ne_half

noncomputable def sandwichedUpClassicalFormulaReal
    (E : Ensemble Y (A × B)) (α : ℝ) (hα : 1 / 2 ≤ α)
    (hα_ne_one : α ≠ 1) : ℝ :=
  (α / (1 - α)) * log2
    (∑ y ∈ Ensemble.conditionalRenyiSupport E,
      (E.probs y : ℝ) * Real.rpow 2
        (((1 - α) / α) * sandwichedConditionalBranch E y α hα hα_ne_one))

/-! A full-rank reference candidate is exactly the negative extended-real
PSD-reference divergence.  This is the bridge used when the source optimizer
is instantiated on a block; it is stated for singular input states as well. -/

theorem sandwichedUpSourceCandidate_eq_neg_referenceE
    (ρ : State (A × B)) (σ : State B) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalSandwichedRenyiUpSourceCandidate σ hσ α hα_pos hα_ne_one =
      -sandwichedRenyiPSDReferenceE ρ
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ) α := by
  by_cases hα_lt_one : α < 1
  · rw [sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one _ _ hα_lt_one]
    have hQpos : 0 < sandwichedRenyiQ ρ.matrix
        (identityTensorStateMatrix (a := A) σ) ρ.pos
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ) α := by
      exact sandwichedRenyiQ_pos_of_state_posDef_reference ρ
        (identityTensorStateMatrix_posDef_of_posDef (a := A) σ hσ) α
    rw [sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero
      ρ
      (identityTensorStateMatrix_posSemidef_of_state (a := A) σ) α
      hQpos.ne']
    unfold conditionalSandwichedRenyiUpSourceCandidate
      sandwichedRenyiPSDReferenceLowAlpha
    simp only [sandwichedRenyiQ_eq_psdTracePower_referenceInner]
    simp [psdTracePower, sandwichedRenyiReferenceInner, EReal.coe_neg]
  · have hα_gt_one : 1 < α :=
      lt_of_le_of_ne (not_lt.mp hα_lt_one) hα_ne_one.symm
    have hτ : (identityTensorStateMatrix (a := A) σ).PosDef :=
      identityTensorStateMatrix_posDef_of_posDef (a := A) σ hσ
    have hsupport : Matrix.Supports ρ.matrix
        (identityTensorStateMatrix (a := A) σ) :=
      Matrix.Supports.of_right_posDef _ _ hτ
    rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ hα_gt_one,
      sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
        ρ hτ.posSemidef α hsupport]
    unfold conditionalSandwichedRenyiUpSourceCandidate
      sandwichedRenyiPSDReferenceHighAlphaFinite
    simp [sandwichedRenyiReferenceInner]

/-- The sandwiched down-arrow conditional entropy under a classical `Y`, in
the source's explicit weighted component-entropy form. -/
theorem conditionalSandwichedRenyiDown_classicalConditioning
    (E : Ensemble Y (A × B)) (α : ℝ) (hα : 1 / 2 ≤ α)
    (hα_ne_one : α ≠ 1) :
    conditionalSandwichedRenyiDownE E α hα hα_ne_one =
      (↑((1 / (1 - α)) * log2
        (∑ y, (E.probs y : ℝ) * Real.rpow 2
          ((1 - α) * sandwichedDownComponentEntropy E y α))) : EReal) := by
  have hQpos := sandwichedDownClassicalQ_pos E α
  have hlog :
      (1 / (1 - α)) * log2
          (sandwichedRenyiQ
            (State.cqConditioningState E).matrix
            (identityTensorStateMatrix (a := A)
              (State.cqConditioningState E).marginalB)
            (State.cqConditioningState E).pos
            (identityTensorStateMatrix_posSemidef_of_state
              (a := A) (State.cqConditioningState E).marginalB) α) =
        (1 / (1 - α)) * log2
          (∑ y, (E.probs y : ℝ) * Real.rpow 2
            ((1 - α) * sandwichedDownComponentEntropy E y α)) := by
    rw [sandwichedRenyiQ_classical_decomposition_support_safe
      E hα hα_ne_one]
    exact sandwichedDownComponentLogFormula E α hα_ne_one
  rcases lt_or_gt_of_ne hα_ne_one with hα_lt_one | hα_gt_one
  · have hQne : sandwichedRenyiQ
          (State.cqConditioningState E).matrix
          (identityTensorStateMatrix (a := A)
            (State.cqConditioningState E).marginalB)
          (State.cqConditioningState E).pos
          (identityTensorStateMatrix_posSemidef_of_state
            (a := A) (State.cqConditioningState E).marginalB) α ≠ 0 :=
      ne_of_gt hQpos
    calc
      conditionalSandwichedRenyiDownE E α hα hα_ne_one =
          (-(sandwichedDownFiniteSupportFormulaReal E α) : EReal) :=
        conditionalSandwichedRenyiDown_classicalConditioning_source_formula_of_lt_one
          E α hα hα_ne_one hα_lt_one hQne
      _ = (↑((1 / (1 - α)) * log2
          (sandwichedRenyiQ
            (State.cqConditioningState E).matrix
            (identityTensorStateMatrix (a := A)
              (State.cqConditioningState E).marginalB)
            (State.cqConditioningState E).pos
            (identityTensorStateMatrix_posSemidef_of_state
              (a := A) (State.cqConditioningState E).marginalB) α)) : EReal) := by
        rw [← EReal.coe_neg]
        apply EReal.coe_eq_coe_iff.mpr
        unfold sandwichedDownFiniteSupportFormulaReal
        rw [sandwichedDownFiniteSupportQ_eq_globalQ_lowAlpha E hα hα_lt_one]
        field_simp [hα_ne_one]
        ring
      _ = (↑((1 / (1 - α)) * log2
          (∑ y, (E.probs y : ℝ) * Real.rpow 2
            ((1 - α) * sandwichedDownComponentEntropy E y α))) : EReal) := by
        rw [hlog]
  · calc
      conditionalSandwichedRenyiDownE E α hα hα_ne_one =
          -(sandwichedRenyiPSDReferenceHighAlphaFinite
            (State.cqConditioningState E)
            (identityTensorStateMatrix (a := A)
              (State.cqConditioningState E).marginalB)
            (identityTensorStateMatrix_posSemidef_of_state
              (a := A) (State.cqConditioningState E).marginalB) α : EReal) :=
        conditionalSandwichedRenyiDown_classicalConditioning_source_formula_of_one_lt
          E α hα hα_ne_one hα_gt_one
      _ = (↑((1 / (1 - α)) * log2
          (sandwichedRenyiQ
            (State.cqConditioningState E).matrix
            (identityTensorStateMatrix (a := A)
              (State.cqConditioningState E).marginalB)
            (State.cqConditioningState E).pos
            (identityTensorStateMatrix_posSemidef_of_state
              (a := A) (State.cqConditioningState E).marginalB) α)) : EReal) := by
        rw [← EReal.coe_neg]
        apply EReal.coe_eq_coe_iff.mpr
        unfold sandwichedRenyiPSDReferenceHighAlphaFinite
        rw [← sandwichedRenyiQ_eq_psdTracePower_referenceInner
          (State.cqConditioningState E)
          (identityTensorStateMatrix_posSemidef_of_state
            (a := A) (State.cqConditioningState E).marginalB) α]
        field_simp [hα_ne_one]
        ring
      _ = (↑((1 / (1 - α)) * log2
          (∑ y, (E.probs y : ℝ) * Real.rpow 2
            ((1 - α) * sandwichedDownComponentEntropy E y α))) : EReal) := by
        rw [hlog]

theorem sandwichedUpSourceCandidate_half_eq_conditionalMaxEntropyCandidate
    (ρ : State (A × B)) (σ : State B) (hσ : σ.matrix.PosDef) :
    ρ.conditionalSandwichedRenyiUpSourceCandidate
        σ hσ (1 / 2 : ℝ) (by norm_num) (by norm_num) =
      ρ.conditionalMaxEntropyCandidate σ := by
  letI : Nonempty A := by
    rcases ρ.nonempty with ⟨a, _⟩
    exact ⟨a⟩
  let d : ℝ := Fintype.card A
  let τ : State (A × B) := (State.maximallyMixed A).prod σ
  have hτ : τ.matrix.PosDef := by
    dsimp [τ]
    exact State.prod_posDef
      (State.maximallyMixed_posDef (a := A)) hσ
  have hd_pos : 0 < d := by
    dsimp [d]
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty A)
  have hscale := sandwichedRenyiQ_real_smul_reference_half ρ
    hτ.posSemidef hd_pos
  have hscale' :
      sandwichedRenyiQ ρ.matrix
          (identityTensorStateMatrix (a := A) σ)
          ρ.pos
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
          (1 / 2 : ℝ) =
        d ^ (1 / 2 : ℝ) *
          sandwichedRenyiQ ρ.matrix τ.matrix ρ.pos τ.pos
            (1 / 2 : ℝ) := by
    simpa [d, τ, identityTensorStateMatrix_eq_card_smul_maximallyMixed_prod] using hscale
  have hQτ :
      sandwichedRenyiQ ρ.matrix τ.matrix ρ.pos τ.pos (1 / 2 : ℝ) =
        ρ.fidelity τ := by
    rw [sandwichedRenyiQ_eq_psdTracePower_inner]
    exact sandwichedRenyiInner_psdTracePower_half_eq_fidelity ρ τ
  have hQ_pos :
      0 < sandwichedRenyiQ ρ.matrix
        (identityTensorStateMatrix (a := A) σ) ρ.pos
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
        (1 / 2 : ℝ) :=
    sandwichedRenyiQ_pos_of_state_posDef_reference ρ
      (identityTensorStateMatrix_posDef_of_posDef (a := A) σ hσ) _
  have hfid_pos : 0 < ρ.fidelity τ := by
    rw [← hQτ]
    rw [hscale'] at hQ_pos
    have hfactor : 0 < d ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hd_pos _
    have hQτ_nonneg : 0 ≤ sandwichedRenyiQ ρ.matrix τ.matrix ρ.pos τ.pos
        (1 / 2 : ℝ) := sandwichedRenyiQ_nonneg ρ.pos τ.pos _
    nlinarith
  have htrace := conditionalSandwichedRenyiUpSourceCandidate_eq_traceTerm
    ρ σ hσ (1 / 2 : ℝ) (by norm_num) (by norm_num)
  rw [htrace]
  change -(1 / ((1 / 2 : ℝ) - 1)) *
      log2 (sandwichedRenyiQ ρ.matrix
        (identityTensorStateMatrix (a := A) σ) ρ.pos
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
        (1 / 2 : ℝ)) = _
  rw [hscale', hQτ]
  rw [log2_mul (ne_of_gt (Real.rpow_pos_of_pos hd_pos _)) hfid_pos.ne']
  have hlog_rpow : log2 (d ^ (1 / 2 : ℝ)) =
      (1 / 2 : ℝ) * log2 d := by
    unfold log2
    rw [Real.log_rpow hd_pos]
    ring
  rw [hlog_rpow]
  rw [conditionalMaxEntropyCandidate_eq_log2_exponentCandidate]
  rw [conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity]
  rw [State.squaredFidelity_eq_fidelity_sq]
  change -(1 / ((1 / 2 : ℝ) - 1)) *
      ((1 / 2 : ℝ) * log2 d + log2 (ρ.fidelity τ)) =
    log2 (d * (ρ.fidelity τ) ^ 2)
  have hsq : (ρ.fidelity τ) ^ 2 =
      ρ.fidelity τ * ρ.fidelity τ := by ring
  rw [hsq]
  rw [log2_mul hd_pos.ne' (mul_ne_zero hfid_pos.ne' hfid_pos.ne')]
  rw [log2_mul hfid_pos.ne' hfid_pos.ne']
  ring

/-! The endpoint bridge below uses the source's positive-definite domain and
the normalized identity regularization to recover the full conditional
max-entropy value set. -/

theorem densityIdentityRegularization_matrix_tendsto_half_source
    [Nonempty B] (σ : State B) :
    Filter.Tendsto
      (fun ε : ℝ => (densityIdentityRegularization σ ε).matrix)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds σ.matrix) := by
  have hraw : Filter.Tendsto
      (fun ε : ℝ => σ.matrix + ε • (1 : CMatrix B))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds σ.matrix) := by
    have hcont : Continuous (fun ε : ℝ =>
        σ.matrix + ε • (1 : CMatrix B)) := by fun_prop
    have hnhds : Filter.Tendsto
        (fun ε : ℝ => σ.matrix + ε • (1 : CMatrix B))
        (nhds (0 : ℝ)) (nhds σ.matrix) := by
      simpa using hcont.tendsto (0 : ℝ)
    exact hnhds.mono_left inf_le_left
  have hscale := densityIdentityRegularization_scale_tendsto σ
  have hscaled := hscale.smul hraw
  have hscaled' : Filter.Tendsto
      (fun ε : ℝ =>
        ((σ.matrix + ε • (1 : CMatrix B)).trace.re)⁻¹ •
          (σ.matrix + ε • (1 : CMatrix B)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds σ.matrix) := by
    simpa using hscaled
  apply hscaled'.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [densityIdentityRegularization_eq_of_pos σ hε,
    stateOfPosDefReference_matrix]

theorem sandwichedRenyiQ_half_eq_conditionalMaxEntropyCandidate
    (ρ : State (A × B)) (σ : State B)
    (hQ : 0 < sandwichedRenyiQ ρ.matrix
      (identityTensorStateMatrix (a := A) σ) ρ.pos
      (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
      (1 / 2 : ℝ)) :
    -(1 / ((1 / 2 : ℝ) - 1)) * log2
        (sandwichedRenyiQ ρ.matrix
          (identityTensorStateMatrix (a := A) σ) ρ.pos
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
          (1 / 2 : ℝ)) =
      ρ.conditionalMaxEntropyCandidate σ := by
  letI : Nonempty A := by
    rcases ρ.nonempty with ⟨a, _⟩
    exact ⟨a⟩
  let d : ℝ := Fintype.card A
  let τ : State (A × B) := (State.maximallyMixed A).prod σ
  have hd_pos : 0 < d := by
    dsimp [d]
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty A)
  have hscale := sandwichedRenyiQ_real_smul_reference_half ρ
    τ.pos hd_pos
  have hscale' :
      sandwichedRenyiQ ρ.matrix
          (identityTensorStateMatrix (a := A) σ) ρ.pos
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
          (1 / 2 : ℝ) =
        d ^ (1 / 2 : ℝ) * sandwichedRenyiQ ρ.matrix τ.matrix ρ.pos τ.pos
          (1 / 2 : ℝ) := by
    simpa [d, τ, identityTensorStateMatrix_eq_card_smul_maximallyMixed_prod]
      using hscale
  have hQτ : sandwichedRenyiQ ρ.matrix τ.matrix ρ.pos τ.pos
      (1 / 2 : ℝ) = ρ.fidelity τ := by
    rw [sandwichedRenyiQ_eq_psdTracePower_inner]
    exact sandwichedRenyiInner_psdTracePower_half_eq_fidelity ρ τ
  have hfid_pos : 0 < ρ.fidelity τ := by
    rw [← hQτ]
    rw [hscale'] at hQ
    have hfactor : 0 < d ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hd_pos _
    have hQτ_nonneg : 0 ≤ sandwichedRenyiQ ρ.matrix τ.matrix ρ.pos τ.pos
        (1 / 2 : ℝ) := sandwichedRenyiQ_nonneg ρ.pos τ.pos _
    nlinarith
  rw [hscale', hQτ]
  rw [log2_mul (ne_of_gt (Real.rpow_pos_of_pos hd_pos _)) hfid_pos.ne']
  have hlog_rpow : log2 (d ^ (1 / 2 : ℝ)) =
      (1 / 2 : ℝ) * log2 d := by
    unfold log2
    rw [Real.log_rpow hd_pos]
    ring
  rw [hlog_rpow, conditionalMaxEntropyCandidate_eq_log2_exponentCandidate,
    conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity,
    State.squaredFidelity_eq_fidelity_sq]
  change -(1 / ((1 / 2 : ℝ) - 1)) *
      ((1 / 2 : ℝ) * log2 d + log2 (ρ.fidelity τ)) =
    log2 (d * (ρ.fidelity τ) ^ 2)
  have hsq : (ρ.fidelity τ) ^ 2 = ρ.fidelity τ * ρ.fidelity τ := by ring
  rw [hsq, log2_mul hd_pos.ne' (mul_ne_zero hfid_pos.ne' hfid_pos.ne'),
    log2_mul hfid_pos.ne' hfid_pos.ne']
  ring

theorem sandwichedUpSourceCandidate_half_regularization_tendsto
    [Nonempty B] (ρ : State (A × B)) (σ : State B)
    (hσ : 0 < ρ.conditionalMaxEntropyExponentCandidate σ) :
    Filter.Tendsto
      (fun ε : ℝ =>
        if hε : 0 < ε then
          ρ.conditionalSandwichedRenyiUpSourceCandidate
            (densityIdentityRegularization σ ε)
            (densityIdentityRegularization_posDef_of_pos σ hε)
            (1 / 2 : ℝ) (by norm_num) (by norm_num)
        else 0)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (ρ.conditionalMaxEntropyCandidate σ)) := by
  letI : Nonempty A := by
    rcases ρ.nonempty with ⟨a, _⟩
    exact ⟨a⟩
  letI : Nonempty B := by
    rcases ρ.nonempty with ⟨_, b⟩
    exact ⟨b⟩
  let d : ℝ := Fintype.card A
  let τ : State (A × B) := (State.maximallyMixed A).prod σ
  have hd_pos : 0 < d := by
    dsimp [d]
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty A)
  have hscale := sandwichedRenyiQ_real_smul_reference_half ρ τ.pos hd_pos
  have hscale' :
      sandwichedRenyiQ ρ.matrix
          (identityTensorStateMatrix (a := A) σ) ρ.pos
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
          (1 / 2 : ℝ) =
        d ^ (1 / 2 : ℝ) * sandwichedRenyiQ ρ.matrix τ.matrix ρ.pos τ.pos
          (1 / 2 : ℝ) := by
    simpa [d, τ, identityTensorStateMatrix_eq_card_smul_maximallyMixed_prod]
      using hscale
  have hQτ : sandwichedRenyiQ ρ.matrix τ.matrix ρ.pos τ.pos
      (1 / 2 : ℝ) = ρ.fidelity τ := by
    rw [sandwichedRenyiQ_eq_psdTracePower_inner]
    exact sandwichedRenyiInner_psdTracePower_half_eq_fidelity ρ τ
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let σF : ℝ → CMatrix B := fun ε =>
    (densityIdentityRegularization σ ε).matrix
  have hσF_tend_matrix : Filter.Tendsto σF l (nhds σ.matrix) := by
    exact densityIdentityRegularization_matrix_tendsto_half_source σ
  let τF : ℝ → CMatrix (A × B) := fun ε =>
    identityTensorStateMatrix (a := A) (densityIdentityRegularization σ ε)
  have hτF_tend : Filter.Tendsto τF l
      (nhds (identityTensorStateMatrix (a := A) σ)) := by
    have h := SubnormalizedState.continuous_kronecker_one_matrix
      (a := A) (b := B)
    exact (h.tendsto σ.matrix).comp hσF_tend_matrix
  have hτF_psd : ∀ ε, (τF ε).PosSemidef := by
    intro ε
    exact identityTensorStateMatrix_posSemidef_of_state (a := A)
      (densityIdentityRegularization σ ε)
  have hQ_tend : Filter.Tendsto
      (fun ε => sandwichedRenyiQ ρ.matrix (τF ε) ρ.pos
        (hτF_psd ε) (1 / 2 : ℝ)) l
      (nhds (sandwichedRenyiQ ρ.matrix
        (identityTensorStateMatrix (a := A) σ) ρ.pos
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
        (1 / 2 : ℝ))) := by
    exact sandwichedRenyiQ_tendsto_of_tendsto_posSemidef
      (α := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) tendsto_const_nhds hτF_tend
      (fun _ => ρ.pos) hτF_psd ρ.pos
      (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
  have hQ_target : 0 < sandwichedRenyiQ ρ.matrix
      (identityTensorStateMatrix (a := A) σ) ρ.pos
      (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
      (1 / 2 : ℝ) := by
    have hexp := hσ
    rw [conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity,
      State.squaredFidelity_eq_fidelity_sq] at hexp
    have hfid_pos : 0 < ρ.fidelity τ := by
      have hexp' : 0 < d * (ρ.fidelity τ) ^ 2 := by
        simpa [d, τ, State.fidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix]
          using hexp
      have hfid_nonneg : 0 ≤ ρ.fidelity τ := State.fidelity_nonneg ρ τ
      have hpow_pos : 0 < (ρ.fidelity τ) ^ 2 := by
        rcases (mul_pos_iff.mp hexp') with h | h
        · exact h.2
        · linarith [hd_pos, h.1]
      nlinarith [hpow_pos, hfid_nonneg]
    rw [hscale', hQτ]
    exact mul_pos (Real.rpow_pos_of_pos hd_pos _) hfid_pos
  have hlog_tend : Filter.Tendsto
      (fun ε => log2 (sandwichedRenyiQ ρ.matrix (τF ε) ρ.pos
        (hτF_psd ε) (1 / 2 : ℝ))) l
      (nhds (log2 (sandwichedRenyiQ ρ.matrix
        (identityTensorStateMatrix (a := A) σ) ρ.pos
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
        (1 / 2 : ℝ)))) := by
    have h := Filter.Tendsto.log hQ_tend hQ_target.ne'
    simpa [log2] using h.div tendsto_const_nhds
      (ne_of_gt (Real.log_pos one_lt_two))
  have hreal_tend : Filter.Tendsto
      (fun ε => -(1 / ((1 / 2 : ℝ) - 1)) *
        log2 (sandwichedRenyiQ ρ.matrix (τF ε) ρ.pos
          (hτF_psd ε) (1 / 2 : ℝ))) l
      (nhds (ρ.conditionalMaxEntropyCandidate σ)) := by
    have h := hlog_tend.const_mul (-1 / ((1 / 2 : ℝ) - 1))
    have htarget := sandwichedRenyiQ_half_eq_conditionalMaxEntropyCandidate
      ρ σ hQ_target
    convert h using 1
    · funext ε
      ring
    · apply congrArg nhds
      have hcoeff : -1 / ((1 / 2 : ℝ) - 1) =
          -(1 / ((1 / 2 : ℝ) - 1)) := by ring
      rw [hcoeff, ← htarget]
  have heq : ∀ᶠ ε in l,
      (if hε : 0 < ε then
        ρ.conditionalSandwichedRenyiUpSourceCandidate
          (densityIdentityRegularization σ ε)
          (densityIdentityRegularization_posDef_of_pos σ hε)
          (1 / 2 : ℝ) (by norm_num) (by norm_num)
      else 0) =
      -(1 / ((1 / 2 : ℝ) - 1)) *
        log2 (sandwichedRenyiQ ρ.matrix (τF ε) ρ.pos
          (hτF_psd ε) (1 / 2 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hsource := conditionalSandwichedRenyiUpSourceCandidate_eq_traceTerm
      ρ (densityIdentityRegularization σ ε)
        (densityIdentityRegularization_posDef_of_pos σ hε)
        (1 / 2 : ℝ) (by norm_num) (by norm_num)
    have hε' : 0 < ε := hε
    rw [dif_pos hε']
    rw [hsource]
    rfl
  exact Filter.Tendsto.congr' (heq.mono fun _ h => h.symm) hreal_tend

theorem sandwichedUpSourceCandidate_half_le_conditionalMaxEntropy
    (ρ : State (A × B)) (σ : State B) (hσ : σ.matrix.PosDef) :
    ρ.conditionalSandwichedRenyiUpSourceCandidate
        σ hσ (1 / 2 : ℝ) (by norm_num) (by norm_num) ≤
      ρ.conditionalMaxEntropy := by
  letI : Nonempty A := by
    rcases ρ.nonempty with ⟨a, _⟩
    exact ⟨a⟩
  letI : Nonempty B := by
    rcases ρ.nonempty with ⟨_, b⟩
    exact ⟨b⟩
  let d : ℝ := Fintype.card A
  let τ : State (A × B) := (State.maximallyMixed A).prod σ
  have hτ : τ.matrix.PosDef := by
    dsimp [τ]
    exact State.prod_posDef
      (State.maximallyMixed_posDef (a := A)) hσ
  have hd_pos : 0 < d := by
    dsimp [d]
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty A)
  have hscale := sandwichedRenyiQ_real_smul_reference_half ρ
    hτ.posSemidef hd_pos
  have hscale' :
      sandwichedRenyiQ ρ.matrix
          (identityTensorStateMatrix (a := A) σ) ρ.pos
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
          (1 / 2 : ℝ) =
        d ^ (1 / 2 : ℝ) *
          sandwichedRenyiQ ρ.matrix τ.matrix ρ.pos τ.pos
            (1 / 2 : ℝ) := by
    simpa [d, τ, identityTensorStateMatrix_eq_card_smul_maximallyMixed_prod] using hscale
  have hQτ :
      sandwichedRenyiQ ρ.matrix τ.matrix ρ.pos τ.pos (1 / 2 : ℝ) =
        ρ.fidelity τ := by
    rw [sandwichedRenyiQ_eq_psdTracePower_inner]
    exact sandwichedRenyiInner_psdTracePower_half_eq_fidelity ρ τ
  have hQ_pos :
      0 < sandwichedRenyiQ ρ.matrix
        (identityTensorStateMatrix (a := A) σ) ρ.pos
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
        (1 / 2 : ℝ) :=
    sandwichedRenyiQ_pos_of_state_posDef_reference ρ
      (identityTensorStateMatrix_posDef_of_posDef (a := A) σ hσ) _
  have hfid_pos : 0 < ρ.fidelity τ := by
    rw [← hQτ]
    rw [hscale'] at hQ_pos
    have hfactor : 0 < d ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hd_pos _
    have hQτ_nonneg : 0 ≤ sandwichedRenyiQ ρ.matrix τ.matrix ρ.pos τ.pos
        (1 / 2 : ℝ) := sandwichedRenyiQ_nonneg ρ.pos τ.pos _
    nlinarith
  have hexp_pos :
      0 < ρ.conditionalMaxEntropyExponentCandidate (a := A) σ := by
    rw [conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity,
      State.squaredFidelity_eq_fidelity_sq]
    exact mul_pos (by positivity) (sq_pos_of_pos hfid_pos)
  rw [sandwichedUpSourceCandidate_half_eq_conditionalMaxEntropyCandidate ρ σ hσ]
  rw [conditionalMaxEntropy_eq_sSup_valueSet]
  exact le_csSup (ρ.conditionalMaxEntropyValueSet_bddAbove (a := A))
    ⟨σ, hexp_pos, rfl⟩

theorem conditionalMaxEntropyExponentCandidate_pos_of_posDef
    (ρ : State (A × B)) (σ : State B) (hσ : σ.matrix.PosDef) :
    0 < ρ.conditionalMaxEntropyExponentCandidate (a := A) σ := by
  letI : Nonempty A := by
    rcases ρ.nonempty with ⟨a, _⟩
    exact ⟨a⟩
  letI : Nonempty B := by
    rcases ρ.nonempty with ⟨_, b⟩
    exact ⟨b⟩
  let d : ℝ := Fintype.card A
  let τ : State (A × B) := (State.maximallyMixed A).prod σ
  have hd_pos : 0 < d := by
    dsimp [d]
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty A)
  have hscale := sandwichedRenyiQ_real_smul_reference_half ρ τ.pos hd_pos
  have hscale' :
      sandwichedRenyiQ ρ.matrix
          (identityTensorStateMatrix (a := A) σ) ρ.pos
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
          (1 / 2 : ℝ) =
        d ^ (1 / 2 : ℝ) * sandwichedRenyiQ ρ.matrix τ.matrix ρ.pos τ.pos
          (1 / 2 : ℝ) := by
    simpa [d, τ, identityTensorStateMatrix_eq_card_smul_maximallyMixed_prod]
      using hscale
  have hQ_pos : 0 < sandwichedRenyiQ ρ.matrix
      (identityTensorStateMatrix (a := A) σ) ρ.pos
      (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
      (1 / 2 : ℝ) :=
    sandwichedRenyiQ_pos_of_state_posDef_reference ρ
      (identityTensorStateMatrix_posDef_of_posDef (a := A) σ hσ) _
  have hQτ_nonneg : 0 ≤ sandwichedRenyiQ ρ.matrix τ.matrix ρ.pos τ.pos
      (1 / 2 : ℝ) := sandwichedRenyiQ_nonneg ρ.pos τ.pos _
  have hfid_pos : 0 < ρ.fidelity τ := by
    have hfactor : 0 < d ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hd_pos _
    have hQτ_pos : 0 < sandwichedRenyiQ ρ.matrix τ.matrix ρ.pos τ.pos
        (1 / 2 : ℝ) := by
      rw [hscale'] at hQ_pos
      rcases (mul_pos_iff.mp hQ_pos) with h | h
      · exact h.2
      · linarith [hfactor, h.1]
    rw [sandwichedRenyiQ_eq_psdTracePower_inner] at hQτ_pos
    rw [sandwichedRenyiInner_psdTracePower_half_eq_fidelity ρ τ] at hQτ_pos
    exact hQτ_pos
  rw [conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity,
    State.squaredFidelity_eq_fidelity_sq]
  exact mul_pos (by positivity) (sq_pos_of_pos hfid_pos)

theorem conditionalSandwichedRenyiUpSource_half_eq_conditionalMaxEntropy
    (ρ : State (A × B)) :
    ρ.conditionalSandwichedRenyiUpSource
        (1 / 2 : ℝ) (by norm_num) (by norm_num) =
      ρ.conditionalMaxEntropy := by
  classical
  letI : Nonempty A := by
    rcases ρ.nonempty with ⟨a, _⟩
    exact ⟨a⟩
  letI : Nonempty B := by
    rcases ρ.nonempty with ⟨_, b⟩
    exact ⟨b⟩
  let S := ρ.conditionalSandwichedRenyiUpSourceValueSet
    (1 / 2 : ℝ) (by norm_num) (by norm_num)
  let M := ρ.conditionalMaxEntropyValueSet (a := A)
  have hS_nonempty : S.Nonempty := by
    simpa [S] using
      ρ.conditionalSandwichedRenyiUpSourceValueSet_nonempty
        (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hM_nonempty : M.Nonempty := by
    simpa [M] using ρ.conditionalMaxEntropyValueSet_nonempty (a := A)
  have hM_bdd : BddAbove M := by
    simpa [M] using ρ.conditionalMaxEntropyValueSet_bddAbove (a := A)
  have hS_bdd : BddAbove S := by
    refine ⟨ρ.conditionalMaxEntropy, ?_⟩
    intro x hx
    rcases hx with ⟨σ, hσ, rfl⟩
    exact sandwichedUpSourceCandidate_half_le_conditionalMaxEntropy ρ σ hσ
  rw [conditionalSandwichedRenyiUpSource_eq,
    conditionalMaxEntropy_eq_sSup_valueSet]
  apply le_antisymm
  · apply csSup_le hS_nonempty
    intro x hx
    rcases hx with ⟨σ, hσ, rfl⟩
    exact le_csSup hM_bdd ⟨σ,
      conditionalMaxEntropyExponentCandidate_pos_of_posDef ρ σ hσ,
      sandwichedUpSourceCandidate_half_eq_conditionalMaxEntropyCandidate
        ρ σ hσ⟩
  · apply csSup_le hM_nonempty
    intro x hx
    rcases hx with ⟨σ, hσ, rfl⟩
    have hlim := sandwichedUpSourceCandidate_half_regularization_tendsto
      ρ σ hσ
    have hbound : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (if hε : 0 < ε then
          ρ.conditionalSandwichedRenyiUpSourceCandidate
            (densityIdentityRegularization σ ε)
            (densityIdentityRegularization_posDef_of_pos σ hε)
            (1 / 2 : ℝ) (by norm_num) (by norm_num)
        else 0) ≤ sSup S := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : 0 < ε := hε
      rw [dif_pos hε']
      exact le_csSup hS_bdd ⟨densityIdentityRegularization σ ε,
        densityIdentityRegularization_posDef_of_pos σ hε', rfl⟩
    exact le_of_tendsto hlim hbound

theorem sandwichedRenyiPSDReferenceE_cq_fullrank_reference_le_classicalFormula_half
    (E : Ensemble Y (A × B)) (F : Ensemble Y B)
    (hF : (F.cqState.reindex (Equiv.prodComm Y B)).matrix.PosDef) :
    -sandwichedRenyiPSDReferenceE
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A)
          (F.cqState.reindex (Equiv.prodComm Y B)))
        (identityTensorStateMatrix_posSemidef_of_state
          (a := A) (F.cqState.reindex (Equiv.prodComm Y B))) (1 / 2 : ℝ) ≤
      (sandwichedUpClassicalFormulaReal E (1 / 2 : ℝ)
        (by norm_num) (by norm_num) : EReal) := by
  classical
  have hα_pos : 0 < (1 / 2 : ℝ) := by norm_num
  have hα_ne_one : (1 / 2 : ℝ) ≠ 1 := by norm_num
  have hq_pos : ∀ y, 0 < (F.probs y : ℝ) := by
    intro y
    exact_mod_cast sandwiched_reference_cq_prob_pos F hF y
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
    have : ∑ y, (E.probs y : ℝ) = 0 := by simp [hp_zero]
    linarith
  have hbranch_le : ∀ y,
      sandwichedFixedReferenceBranchValue E F y (1 / 2 : ℝ) hF
          hα_pos hα_ne_one ≤
        sandwichedConditionalBranch E y (1 / 2 : ℝ) (by norm_num)
          (by norm_num) := by
    intro y
    have hyF : (F.states y).matrix.PosDef :=
      sandwiched_reference_cq_state_posDef F hF y
    calc
      sandwichedFixedReferenceBranchValue E F y (1 / 2 : ℝ) hF
          hα_pos hα_ne_one =
          (E.states y).conditionalSandwichedRenyiUpSourceCandidate
            (F.states y) hyF (1 / 2 : ℝ) hα_pos hα_ne_one := rfl
      _ ≤ (E.states y).conditionalMaxEntropy :=
        sandwichedUpSourceCandidate_half_le_conditionalMaxEntropy
          (E.states y) (F.states y) hyF
      _ = sandwichedConditionalBranch E y (1 / 2 : ℝ) (by norm_num)
          (by norm_num) := by
        symm
        unfold sandwichedConditionalBranch
        simpa only [one_div] using
          conditionalSandwichedRenyiUpFiniteOrder_half (E.states y)
  let k : ℝ := (1 - (1 / 2 : ℝ)) / (1 / 2 : ℝ)
  let c : Y → ℝ := fun y =>
    sandwichedFixedReferenceBranchValue E F y (1 / 2 : ℝ) hF
      hα_pos hα_ne_one
  let h : Y → ℝ := fun y =>
    sandwichedConditionalBranch E y (1 / 2 : ℝ) (by norm_num) (by norm_num)
  let r : Y → ℝ := fun y =>
    (E.probs y : ℝ) * Real.rpow 2 (k * c y)
  let R : Y → ℝ := fun y =>
    (E.probs y : ℝ) * Real.rpow 2 (k * h y)
  have hk_pos : 0 < k := by
    dsimp [k]
    norm_num
  have hr_nonneg : ∀ y, 0 ≤ r y := by
    intro y
    dsimp [r]
    exact mul_nonneg (E.prob_nonneg y) (Real.rpow_nonneg (by norm_num) _)
  have hr_le_R : ∀ y, r y ≤ R y := by
    intro y
    have hexp : k * c y ≤ k * h y :=
      mul_le_mul_of_nonneg_left (hbranch_le y) hk_pos.le
    have hpow : Real.rpow 2 (k * c y) ≤ Real.rpow 2 (k * h y) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    dsimp [r, R]
    exact mul_le_mul_of_nonneg_left hpow (E.prob_nonneg y)
  have hsum_le : (∑ y, r y) ≤ ∑ y, R y :=
    Finset.sum_le_sum fun y _ => hr_le_R y
  have hr_pos : 0 < ∑ y, r y := by
    apply Finset.sum_pos'
    · intro y hy
      exact hr_nonneg y
    · rcases hp_exists with ⟨y, hy⟩
      refine ⟨y, Finset.mem_univ y, ?_⟩
      dsimp [r]
      exact mul_pos hy (Real.rpow_pos_of_pos (by norm_num) _)
  have hR_pos : 0 < ∑ y, R y := hr_pos.trans_le hsum_le
  have hscalar_pos :
      0 < sandwichedScalarPower r (fun y => (F.probs y : ℝ))
          (1 / 2 : ℝ) := by
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
        (Real.rpow_pos_of_pos hry (1 / 2 : ℝ))
        (Real.rpow_pos_of_pos (hq_pos y) (1 - (1 / 2 : ℝ)))
  have hscalar := sandwichedScalarPower_le_sum_rpow_of_nonneg
    r (fun y => (F.probs y : ℝ)) (1 / 2 : ℝ) hr_nonneg hq_pos hq_sum
      hα_pos (by norm_num)
  have hsum_pow : (∑ y, r y) ^ (1 / 2 : ℝ) ≤
      (∑ y, R y) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hr_pos.le hsum_le (by norm_num)
  have hscalar_le :
      sandwichedScalarPower r (fun y => (F.probs y : ℝ)) (1 / 2 : ℝ) ≤
        (∑ y, R y) ^ (1 / 2 : ℝ) := hscalar.trans hsum_pow
  have hlog_le :
      log2 (sandwichedScalarPower r (fun y => (F.probs y : ℝ))
        (1 / 2 : ℝ)) ≤ log2 ((∑ y, R y) ^ (1 / 2 : ℝ)) := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hscalar_pos hscalar_le)
      (le_of_lt (Real.log_pos (by norm_num)))
  have hlog_pow : log2 ((∑ y, R y) ^ (1 / 2 : ℝ)) =
      (1 / 2 : ℝ) * log2 (∑ y, R y) := by
    unfold log2
    rw [Real.log_rpow hR_pos]
    ring
  have hreal :
      (1 / (1 - (1 / 2 : ℝ))) *
          log2 (sandwichedScalarPower r (fun y => (F.probs y : ℝ))
            (1 / 2 : ℝ)) ≤
        ((1 / 2 : ℝ) / (1 - (1 / 2 : ℝ))) *
          log2 (∑ y, R y) := by
    have h := mul_le_mul_of_nonneg_left hlog_le (by norm_num :
      0 ≤ 1 / (1 - (1 / 2 : ℝ)))
    rw [hlog_pow] at h
    calc
      _ ≤ (1 / (1 - (1 / 2 : ℝ))) *
          ((1 / 2 : ℝ) * log2 (∑ y, R y)) := h
      _ = _ := by ring
  rw [sandwichedRenyiPSDReferenceE_cq_fullrank_reference_formula
    E F hF (1 / 2 : ℝ) hα_pos hα_ne_one]
  apply EReal.coe_le_coe_iff.mpr
  rw [sandwichedUpFixedReferenceFormulaReal_eq_branchFormula
    E F hF (1 / 2 : ℝ) hα_pos hα_ne_one]
  rw [sandwichedUpFixedReferenceBranchFormulaReal_eq_log_scalarPower
    E F hF (1 / 2 : ℝ) hα_pos hα_ne_one]
  have hsupport_sum :
      (∑ y ∈ E.conditionalRenyiSupport,
        (E.probs y : ℝ) * Real.rpow 2 (k * h y)) = ∑ y, R y := by
    rw [← Finset.sum_subset (Finset.subset_univ E.conditionalRenyiSupport)]
    intro y hy hnot
    have hpy : E.probs y = 0 :=
      (E.not_mem_conditionalRenyiSupport_iff y).mp hnot
    dsimp [R]
    simp [hpy]
  unfold sandwichedUpClassicalFormulaReal
  rw [hsupport_sum]
  simpa [h, R, r, k, c] using hreal

theorem sandwichedRenyiPSDReferenceE_cq_fullrank_reference_le_classicalFormula_of_half_lt_lt_one
    (E : Ensemble Y (A × B)) (F : Ensemble Y B)
    (hF : (F.cqState.reindex (Equiv.prodComm Y B)).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    -sandwichedRenyiPSDReferenceE
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A)
          (F.cqState.reindex (Equiv.prodComm Y B)))
        (identityTensorStateMatrix_posSemidef_of_state
          (a := A) (F.cqState.reindex (Equiv.prodComm Y B))) α ≤
      (sandwichedUpClassicalFormulaReal E α hα_half.le
        (ne_of_lt hα_lt_one) : EReal) := by
  classical
  have hα_pos : 0 < α := lt_trans (by norm_num) hα_half
  have hα_ne_one : α ≠ 1 := ne_of_lt hα_lt_one
  have hq_pos : ∀ y, 0 < (F.probs y : ℝ) := by
    intro y
    exact_mod_cast sandwiched_reference_cq_prob_pos F hF y
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
        sandwichedConditionalBranch E y α hα_half.le hα_ne_one := by
    intro y
    have hyF : (F.states y).matrix.PosDef :=
      sandwiched_reference_cq_state_posDef F hF y
    have hsource_bdd :=
      (E.states y).conditionalSandwichedRenyiUpSourceValueSet_bddAbove_of_half_lt_lt_one
        hα_half hα_lt_one
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
      _ = sandwichedConditionalBranch E y α hα_half.le hα_ne_one := by
        symm
        exact conditionalSandwichedRenyiUpFiniteOrder_of_pos_ne_one_ne_half
          (E.states y) hα_pos hα_ne_one (by linarith)
  let k : ℝ := (1 - α) / α
  let c : Y → ℝ := fun y =>
    sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one
  let h : Y → ℝ := fun y =>
    sandwichedConditionalBranch E y α hα_half.le hα_ne_one
  let r : Y → ℝ := fun y =>
    (E.probs y : ℝ) * Real.rpow 2 (k * c y)
  let R : Y → ℝ := fun y =>
    (E.probs y : ℝ) * Real.rpow 2 (k * h y)
  have hk_pos : 0 < k := by
    dsimp [k]
    exact div_pos (by linarith) hα_pos
  have hr_nonneg : ∀ y, 0 ≤ r y := by
    intro y
    dsimp [r]
    exact mul_nonneg (E.prob_nonneg y) (Real.rpow_nonneg (by norm_num) _)
  have hR_nonneg : ∀ y, 0 ≤ R y := by
    intro y
    dsimp [R]
    exact mul_nonneg (E.prob_nonneg y) (Real.rpow_nonneg (by norm_num) _)
  have hr_le_R : ∀ y, r y ≤ R y := by
    intro y
    have hexp : k * c y ≤ k * h y := by
      exact mul_le_mul_of_nonneg_left (hbranch_le y) hk_pos.le
    have hpow : Real.rpow 2 (k * c y) ≤ Real.rpow 2 (k * h y) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    dsimp [r, R]
    exact mul_le_mul_of_nonneg_left hpow (E.prob_nonneg y)
  have hsum_le : (∑ y, r y) ≤ ∑ y, R y := by
    exact Finset.sum_le_sum fun y _ => hr_le_R y
  have hr_pos : 0 < ∑ y, r y := by
    apply Finset.sum_pos'
    · intro y hy
      exact hr_nonneg y
    · rcases hp_exists with ⟨y, hy⟩
      refine ⟨y, Finset.mem_univ y, ?_⟩
      dsimp [r]
      exact mul_pos hy (Real.rpow_pos_of_pos (by norm_num) _)
  have hR_pos : 0 < ∑ y, R y := hr_pos.trans_le hsum_le
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
  have hscalar := sandwichedScalarPower_le_sum_rpow_of_nonneg
    r (fun y => (F.probs y : ℝ)) α hr_nonneg hq_pos hq_sum hα_pos hα_lt_one
  have hsum_pow : (∑ y, r y) ^ α ≤ (∑ y, R y) ^ α :=
    Real.rpow_le_rpow hr_pos.le hsum_le hα_pos.le
  have hscalar_le :
      sandwichedScalarPower r (fun y => (F.probs y : ℝ)) α ≤
      (∑ y, R y) ^ α := hscalar.trans (hsum_pow)
  have hlog_le :
      log2 (sandwichedScalarPower r (fun y => (F.probs y : ℝ)) α) ≤
      log2 ((∑ y, R y) ^ α) := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hscalar_pos hscalar_le)
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
    have hcoeff : 0 ≤ 1 / (1 - α) := by positivity
    have h := mul_le_mul_of_nonneg_left hlog_le hcoeff
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

/-! The strict low-alpha regularization handoff for an arbitrary reference. -/
theorem conditionalSandwichedRenyiUp_lowAlpha_regularization_input_tendsto
    (E : Ensemble Y (A × B)) (σ : State (B × Y)) (α : ℝ)
    (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hQpos : 0 < sandwichedRenyiQ
      (State.cqConditioningState E).matrix
      (identityTensorStateMatrix (a := A) σ)
      (State.cqConditioningState E).pos
      (identityTensorStateMatrix_posSemidef_of_state (a := A) σ) α) :
    Filter.Tendsto
      (sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve
        (State.cqConditioningState E)
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ) α)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (sandwichedRenyiPSDReferenceLowAlpha
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ) α)) := by
  exact sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve_tendsto
    (State.cqConditioningState E)
    (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
    α hα_half hα_lt_one hQpos

private theorem sandwichedRenyiQ_real_smul_reference_of_pos
    (ρ : State (A × (B × Y))) {τ : CMatrix (A × (B × Y))}
    (hτ : τ.PosSemidef) {scale : ℝ} (hscale_pos : 0 < scale) (α : ℝ) (hα_pos : 0 < α) :
    sandwichedRenyiQ ρ.matrix (scale • τ) ρ.pos
        (Matrix.PosSemidef.smul hτ hscale_pos.le) α =
      scale ^ (1 - α) * sandwichedRenyiQ ρ.matrix τ ρ.pos hτ α := by
  have hscale := sandwichedRenyiReferenceInner_psdTracePower_real_smul_reference
    ρ hτ hscale_pos.le α
  have hfactor :
      (scale ^ ((1 - α) / (2 * α)) * scale ^ ((1 - α) / (2 * α))) ^ α =
        scale ^ (1 - α) := by
    have hmul :
        scale ^ ((1 - α) / (2 * α)) * scale ^ ((1 - α) / (2 * α)) =
          scale ^ (((1 - α) / (2 * α)) + ((1 - α) / (2 * α))) := by
      rw [Real.rpow_add hscale_pos]
    rw [hmul, ← Real.rpow_mul hscale_pos.le]
    congr 1
    field_simp [ne_of_gt hα_pos]
    ring
  rw [sandwichedRenyiQ_eq_psdTracePower_referenceInner,
    sandwichedRenyiQ_eq_psdTracePower_referenceInner]
  rw [hscale, hfactor]

omit [Fintype A] [Fintype B] [DecidableEq B] [Fintype Y] [DecidableEq Y] in
theorem kroneckerMap_one_real_smul
    (c : ℝ) (M : CMatrix (B × Y)) :
    Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix A)
        ((c : ℂ) • M) =
      (c : ℂ) • Matrix.kroneckerMap (fun x y => x * y)
        (1 : CMatrix A) M := by
  ext i j
  simp [Matrix.kroneckerMap_apply, Matrix.smul_apply]
  ring

omit [Fintype A] [Fintype B] [DecidableEq B] [Fintype Y] [DecidableEq Y] in
theorem kroneckerMap_one_smul_real
    (c : ℝ) (M : CMatrix (B × Y)) :
    Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix A)
        (c • M) =
      c • Matrix.kroneckerMap (fun x y => x * y)
        (1 : CMatrix A) M := by
  ext i j
  simp [Matrix.kroneckerMap_apply, Matrix.smul_apply]
  ring

omit [Fintype A] [Fintype B] [DecidableEq B] [Fintype Y] [DecidableEq Y] in
theorem kroneckerMap_one_add
    (M N : CMatrix (B × Y)) :
    Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix A) (M + N) =
      Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix A) M +
        Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix A) N := by
  ext i j
  simp [Matrix.kroneckerMap_apply, Matrix.add_apply]
  ring

omit [Fintype A] [Fintype B] [Fintype Y] in
theorem kroneckerMap_one_one :
    Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix A)
        (1 : CMatrix (B × Y)) = (1 : CMatrix (A × (B × Y))) := by
  ext i j
  simp [Matrix.kroneckerMap_apply, Matrix.one_apply]
  by_cases h1 : i.1 = j.1 <;> by_cases h2 : i.2 = j.2
  · have hij : i = j := Prod.ext h1 h2
    simp [hij]
  · have hij : ¬ i = j := by
      intro hij
      exact h2 (congrArg Prod.snd hij)
    simp [h2, hij]
  · have hij : ¬ i = j := by
      intro hij
      exact h1 (congrArg Prod.fst hij)
    simp [h1, h2, hij]
  · have hij : ¬ i = j := by
      intro hij
      exact h1 (congrArg Prod.fst hij)
    simp [h2, hij]

theorem conditionalSandwichedRenyiUp_candidateE_fullRankApprox_tendsto_of_lowAlpha
    [Nonempty B]
    (E : Ensemble Y (A × B)) (σ : State (B × Y)) (α : ℝ)
    (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hQpos : 0 < sandwichedRenyiQ
      (State.cqConditioningState E).matrix
      (identityTensorStateMatrix (a := A) σ)
      (State.cqConditioningState E).pos
      (identityTensorStateMatrix_posSemidef_of_state (a := A) σ) α) :
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
  have hlow := conditionalSandwichedRenyiUp_lowAlpha_regularization_input_tendsto
    E σ α hα_half hα_lt_one hQpos
  have hreal :
      Filter.Tendsto
        (fun δ : ℝ =>
          -(sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve
            ρ hτ α (ε δ)) + log2 (scale δ))
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 1))
        (nhds (-sandwichedRenyiPSDReferenceLowAlpha ρ τ hτ α)) := by
    have hlow' := hlow.comp hε
    have hlog : Filter.Tendsto (fun δ : ℝ => log2 (scale δ))
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds 0) := by
      simpa [scale] using log2_one_sub_tendsto_zero
    have hneg := hlow'.neg
    convert hneg.add hlog using 1
    all_goals simp [ρ, τ]
  have hevent : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioo 0 1),
      0 < δ ∧ δ < 1 := by
    exact self_mem_nhdsWithin
  have hpath : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioo 0 1),
      (fun δ : ℝ =>
        -sandwichedRenyiPSDReferenceE ρ
          (identityTensorStateMatrix (a := A)
            (fullRankApproxMaximallyMixedStatePath σ δ))
          (identityTensorStateMatrix_posSemidef_of_state (a := A)
            (fullRankApproxMaximallyMixedStatePath σ δ)) α) δ =
        ((-(sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve
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
        (identityTensorStateMatrix (a := A)
          (fullRankApproxMaximallyMixedStatePath σ δ)) =
          scale δ •
            sandwichedRenyiReferenceRegularization τ (ε δ) := by
      change Matrix.kroneckerMap (fun x y => x * y)
        (1 : CMatrix A)
          (fullRankApproxMaximallyMixedStatePath σ δ).matrix = _
      rw [hpath_matrix]
      calc
        Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix A)
              (((1 - δ : ℝ) : ℂ) •
                sandwichedRenyiReferenceRegularization σ.matrix
                  (δ / ((1 - δ) * (Fintype.card (B × Y) : ℝ)))) =
            Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix A)
              ((1 - δ) •
                sandwichedRenyiReferenceRegularization σ.matrix
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
    have hτδ_pd :
        (fullRankApproxMaximallyMixedStatePath σ δ).matrix.PosDef := by
      have hδmem : δ ∈ Set.Ioo (0 : ℝ) 1 := hδ
      simpa [fullRankApproxMaximallyMixedStatePath, fullRankApproxStatePath,
        hδmem] using
        (fullRankApproxState_posDef_of_noise σ
          (State.maximallyMixed (B × Y))
          (State.maximallyMixed_posDef)
          hδ.1.le hδ.2.le hδ.1)
    have href_pd :
        (identityTensorStateMatrix (a := A)
          (fullRankApproxMaximallyMixedStatePath σ δ)).PosDef :=
      identityTensorStateMatrix_posDef_of_posDef (a := A)
        (fullRankApproxMaximallyMixedStatePath σ δ) hτδ_pd
    have hQreg : 0 < sandwichedRenyiQ ρ.matrix
        (sandwichedRenyiReferenceRegularization τ (ε δ)) ρ.pos
        (sandwichedRenyiReferenceRegularization_posDef hτ hε_pos).posSemidef α := by
      exact sandwichedRenyiQ_pos_of_state_posDef_reference ρ
        (sandwichedRenyiReferenceRegularization_posDef hτ hε_pos) α
    have hQpath_eq :
        sandwichedRenyiQ ρ.matrix
            (identityTensorStateMatrix (a := A)
              (fullRankApproxMaximallyMixedStatePath σ δ))
            ρ.pos href_pd.posSemidef α =
          sandwichedRenyiQ ρ.matrix
            (scale δ • sandwichedRenyiReferenceRegularization τ (ε δ))
            ρ.pos
            (Matrix.PosSemidef.smul
              (sandwichedRenyiReferenceRegularization_posDef hτ hε_pos).posSemidef
              (by exact_mod_cast hscale_pos.le)) α := by
      congr 1
    have hQpath_pos : 0 < sandwichedRenyiQ ρ.matrix
        (identityTensorStateMatrix (a := A)
          (fullRankApproxMaximallyMixedStatePath σ δ))
        ρ.pos href_pd.posSemidef α := by
      rw [hQpath_eq]
      have hQscale := sandwichedRenyiQ_real_smul_reference_of_pos ρ
        (sandwichedRenyiReferenceRegularization_posDef hτ hε_pos).posSemidef
        hscale_pos α (by linarith)
      rw [hQscale]
      exact mul_pos (Real.rpow_pos_of_pos hscale_pos (1 - α)) hQreg
    have hlow_eq :
        sandwichedRenyiPSDReferenceLowAlpha ρ
            (identityTensorStateMatrix (a := A)
              (fullRankApproxMaximallyMixedStatePath σ δ))
            href_pd.posSemidef α =
          sandwichedRenyiPSDReferenceLowAlpha ρ
            (scale δ • sandwichedRenyiReferenceRegularization τ (ε δ))
            (Matrix.PosSemidef.smul
              (sandwichedRenyiReferenceRegularization_posDef hτ hε_pos).posSemidef
              (by exact_mod_cast hscale_pos.le)) α := by
      congr 1
    rw [sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one _ _ hα_lt_one,
      sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero]
    · rw [hlow_eq]
      have hQscale := sandwichedRenyiQ_real_smul_reference_of_pos ρ
        (sandwichedRenyiReferenceRegularization_posDef hτ hε_pos).posSemidef
        hscale_pos α (by linarith)
      unfold sandwichedRenyiPSDReferenceLowAlpha
      rw [← EReal.coe_neg]
      apply EReal.coe_eq_coe_iff.mpr
      rw [hQscale]
      simp only [log2]
      rw [Real.log_mul
        (ne_of_gt (Real.rpow_pos_of_pos hscale_pos (1 - α)))
        (ne_of_gt hQreg)]
      have hlogscale : Real.log (scale δ ^ (1 - α)) =
          (1 - α) * Real.log (scale δ) := by
        rw [Real.log_rpow hscale_pos]
      rw [hlogscale]
      norm_num [sandwichedRenyiPSDReferenceLowAlphaRegularizedInputCurve,
        sandwichedRenyiPSDReferenceLowAlpha, hε_nonneg, scale]
      simp only [log2]
      have hαsub : α - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hα_lt_one)
      field_simp [hαsub]
      ring
    · exact (ne_of_gt hQpath_pos)
  have htarget :
      -sandwichedRenyiPSDReferenceE ρ τ hτ α =
        (-sandwichedRenyiPSDReferenceLowAlpha ρ τ hτ α : EReal) := by
    rw [sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one _ _ hα_lt_one,
      sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero _ _ _ hQpos.ne']
  rw [htarget]
  have hpath' := hpath.mono (fun _ h => h.symm)
  exact Filter.Tendsto.congr' hpath' (EReal.tendsto_coe.mpr hreal)


end State

end

end QIT
