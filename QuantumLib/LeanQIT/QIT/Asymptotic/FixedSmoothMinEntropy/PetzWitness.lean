/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Asymptotic.FixedSmoothMinEntropy.FixedReference

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker NNReal
open Filter

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
namespace State
/-! ## Fixed-reference feasible witnesses -/

/-- Fixed-reference Petz threshold exponent used in the TCR smooth-min lower
bound. -/
def petzSmoothMinThresholdExponent
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α hα_pos hα_ne_one -
    (1 / (α - 1)) * log2 (2 / ε ^ 2)

/-- Fixed-reference Petz threshold scale, i.e. the right-hand scalar
`2^{-λ}` for `petzSmoothMinThresholdExponent`. -/
def petzSmoothMinThresholdScale
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  Real.rpow 2
    (-(ρ.petzSmoothMinThresholdExponent hρ σ hσ ε α hα_pos hα_ne_one))

/-- Fixed-reference Petz threshold exponent for an arbitrary left state and a
full-rank reference side. This is the source-domain version of
`petzSmoothMinThresholdExponent`: only the reference matrix carries a
positive-definiteness witness. -/
def petzSmoothMinThresholdExponentFullReference
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α hα_pos hα_ne_one -
    (1 / (α - 1)) * log2 (2 / ε ^ 2)

/-- Full-reference Petz threshold scale for arbitrary left states. -/
def petzSmoothMinThresholdScaleFullReference
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  Real.rpow 2
    (-(ρ.petzSmoothMinThresholdExponentFullReference σ hσ ε α hα_pos hα_ne_one))

theorem petzSmoothMinThresholdScale_pos
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    0 < ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one := by
  unfold petzSmoothMinThresholdScale
  exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _

theorem petzSmoothMinThresholdScaleFullReference_pos
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    0 < ρ.petzSmoothMinThresholdScaleFullReference σ hσ ε α hα_pos hα_ne_one := by
  unfold petzSmoothMinThresholdScaleFullReference
  exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _

theorem petzSmoothMinThresholdExponentFullReference_eq_neg_log2_scale
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.petzSmoothMinThresholdExponentFullReference σ hσ ε α hα_pos hα_ne_one =
      -log2 (ρ.petzSmoothMinThresholdScaleFullReference σ hσ ε α
        hα_pos hα_ne_one) := by
  simpa [petzSmoothMinThresholdScaleFullReference] using
    (neg_log2_rpow_two_neg
      (ρ.petzSmoothMinThresholdExponentFullReference σ hσ ε α hα_pos hα_ne_one)).symm

theorem petzSmoothMinThresholdScale_eq_entropyPenalty
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    {ε α : ℝ} (hε_pos : 0 < ε)
    (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one =
      Real.rpow 2
          (-(ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
            hα_pos hα_ne_one)) *
        (2 / ε ^ 2) ^ (1 / (α - 1)) := by
  have hx : 0 < 2 / ε ^ 2 := by
    exact div_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hε_pos)
  simpa [petzSmoothMinThresholdScale, petzSmoothMinThresholdExponent] using
    (rpow_two_neg_sub_mul_log2_pos
      (H := ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α hα_pos hα_ne_one)
      (gamma := 1 / (α - 1)) (x := 2 / ε ^ 2) hx)

theorem petzSmoothMinThresholdScale_rpow_one_sub_alpha_mul_traceTerm_eq
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    {ε α : ℝ} (hε_pos : 0 < ε) (hα_gt : 1 < α) :
    ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ^ (1 - α) *
      ρ.conditionalPetzRenyiTraceTerm σ α =
        ε ^ 2 / 2 := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let H : ℝ := ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α hα_pos hα_ne_one
  let T : ℝ := ρ.conditionalPetzRenyiTraceTerm σ α
  let x : ℝ := 2 / ε ^ 2
  let lam : ℝ := ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
  have hx_pos : 0 < x := by
    exact div_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hε_pos)
  have hT_pos : 0 < T := by
    simpa [T] using
      conditionalPetzRenyiTraceTerm_pos_of_posDef (ρ := ρ) hρ (σ := σ) hσ α
  have hT :
      Real.rpow 2 ((1 - α) * H) = T := by
    simpa [H, T, hα_pos, hα_ne_one] using
      rpow_two_one_sub_alpha_mul_conditionalPetzRenyiEntropyCandidate
        (ρ := ρ) hρ (σ := σ) hσ α hα_pos hα_ne_one
  have hlam_def :
      lam = Real.rpow 2 (-(H - (1 / (α - 1)) * log2 x)) := by
    simp [lam, petzSmoothMinThresholdScale, petzSmoothMinThresholdExponent,
      H, x]
  have hpow_lam :
      lam ^ (1 - α) =
        Real.rpow 2 (-(H - (1 / (α - 1)) * log2 x) * (1 - α)) := by
    rw [hlam_def]
    exact (Real.rpow_mul (x := (2 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2)
      (-(H - (1 / (α - 1)) * log2 x)) (1 - α)).symm
  have hexp :
      -(H - (1 / (α - 1)) * log2 x) * (1 - α) =
        (α - 1) * H + -log2 x := by
    have hden : α - 1 ≠ 0 := sub_ne_zero.mpr hα_ne_one
    field_simp [hden]
    ring
  have hH_inv :
      Real.rpow 2 ((α - 1) * H) = T⁻¹ := by
    have hrewrite : (α - 1) * H = -((1 - α) * H) := by ring
    calc
      Real.rpow 2 ((α - 1) * H) =
          Real.rpow 2 (-((1 - α) * H)) := by rw [hrewrite]
      _ = (Real.rpow 2 ((1 - α) * H))⁻¹ := by
          exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) ((1 - α) * H)
      _ = T⁻¹ := by rw [hT]
  have hx_inv : Real.rpow 2 (-log2 x) = x⁻¹ := by
    calc
      Real.rpow 2 (-log2 x) =
          (Real.rpow 2 (log2 x))⁻¹ := by
        exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (log2 x)
      _ = x⁻¹ := by rw [rpow_two_log2_pos hx_pos]
  have hmain : lam ^ (1 - α) * T = x⁻¹ := by
    calc
      lam ^ (1 - α) * T =
          Real.rpow 2 ((α - 1) * H + -log2 x) * T := by
        rw [hpow_lam, hexp]
      _ =
          (Real.rpow 2 ((α - 1) * H) * Real.rpow 2 (-log2 x)) * T := by
        exact congrArg (fun y : ℝ => y * T)
          (Real.rpow_add (x := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2)
            ((α - 1) * H) (-log2 x))
      _ = (T⁻¹ * x⁻¹) * T := by rw [hH_inv, hx_inv]
      _ = x⁻¹ := by
        field_simp [ne_of_gt hT_pos]
  have hx_inv_eq : x⁻¹ = ε ^ 2 / 2 := by
    dsimp [x]
    field_simp [pow_ne_zero 2 (ne_of_gt hε_pos)]
  simpa [lam, T, hα_pos, hα_ne_one] using hmain.trans hx_inv_eq

theorem petzSmoothMinThresholdScaleFullReference_rpow_one_sub_alpha_mul_traceTerm_eq
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    {ε α : ℝ} (hε_pos : 0 < ε) (hα_gt : 1 < α) :
    ρ.petzSmoothMinThresholdScaleFullReference σ hσ ε α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ^ (1 - α) *
      ρ.conditionalPetzRenyiTraceTerm σ α =
        ε ^ 2 / 2 := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let H : ℝ :=
    ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α hα_pos hα_ne_one
  let T : ℝ := ρ.conditionalPetzRenyiTraceTerm σ α
  let x : ℝ := 2 / ε ^ 2
  let lam : ℝ := ρ.petzSmoothMinThresholdScaleFullReference σ hσ ε α hα_pos hα_ne_one
  have hx_pos : 0 < x := by
    exact div_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hε_pos)
  have hT_pos : 0 < T := by
    simpa [T] using
      conditionalPetzRenyiTraceTerm_pos_of_fullReference (ρ := ρ) (σ := σ) hσ α
  have hT :
      Real.rpow 2 ((1 - α) * H) = T := by
    dsimp [H, conditionalPetzRenyiEntropyCandidateFullReference]
    have hden : 1 - α ≠ 0 := sub_ne_zero.mpr hα_ne_one.symm
    rw [show (1 - α) * ((1 / (1 - α)) * log2 T) = log2 T by
      field_simp [hden]]
    exact rpow_two_log2_pos hT_pos
  have hlam_def :
      lam = Real.rpow 2 (-(H - (1 / (α - 1)) * log2 x)) := by
    simp [lam, petzSmoothMinThresholdScaleFullReference,
      petzSmoothMinThresholdExponentFullReference, H, x]
  have hpow_lam :
      lam ^ (1 - α) =
        Real.rpow 2 (-(H - (1 / (α - 1)) * log2 x) * (1 - α)) := by
    rw [hlam_def]
    exact (Real.rpow_mul (x := (2 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2)
      (-(H - (1 / (α - 1)) * log2 x)) (1 - α)).symm
  have hexp :
      -(H - (1 / (α - 1)) * log2 x) * (1 - α) =
        (α - 1) * H + -log2 x := by
    have hden : α - 1 ≠ 0 := sub_ne_zero.mpr hα_ne_one
    field_simp [hden]
    ring
  have hH_inv :
      Real.rpow 2 ((α - 1) * H) = T⁻¹ := by
    have hrewrite : (α - 1) * H = -((1 - α) * H) := by ring
    calc
      Real.rpow 2 ((α - 1) * H) =
          Real.rpow 2 (-((1 - α) * H)) := by rw [hrewrite]
      _ = (Real.rpow 2 ((1 - α) * H))⁻¹ := by
          exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) ((1 - α) * H)
      _ = T⁻¹ := by rw [hT]
  have hx_inv : Real.rpow 2 (-log2 x) = x⁻¹ := by
    calc
      Real.rpow 2 (-log2 x) =
          (Real.rpow 2 (log2 x))⁻¹ := by
        exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (log2 x)
      _ = x⁻¹ := by rw [rpow_two_log2_pos hx_pos]
  have hmain : lam ^ (1 - α) * T = x⁻¹ := by
    calc
      lam ^ (1 - α) * T =
          Real.rpow 2 ((α - 1) * H + -log2 x) * T := by
        rw [hpow_lam, hexp]
      _ =
          (Real.rpow 2 ((α - 1) * H) * Real.rpow 2 (-log2 x)) * T := by
        exact congrArg (fun y : ℝ => y * T)
          (Real.rpow_add (x := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2)
            ((α - 1) * H) (-log2 x))
      _ = (T⁻¹ * x⁻¹) * T := by rw [hH_inv, hx_inv]
      _ = x⁻¹ := by
        field_simp [ne_of_gt hT_pos]
  have hx_inv_eq : x⁻¹ = ε ^ 2 / 2 := by
    dsimp [x]
    field_simp [pow_ne_zero 2 (ne_of_gt hε_pos)]
  simpa [lam, T, hα_pos, hα_ne_one] using hmain.trans hx_inv_eq

theorem SubnormalizedState.ConditionalMinEntropyFeasible.of_le_petzSmoothMinThresholdScale
    {ρ' : SubnormalizedState (Prod a b)}
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1)
    (hbound :
      ρ'.matrix ≤
        ((ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one : ℝ) : ℂ) •
          identityTensorStateMatrix (a := a) σ) :
    SubnormalizedState.ConditionalMinEntropyFeasible (a := a) ρ' σ.toSubnormalized
      (ρ.petzSmoothMinThresholdExponent hρ σ hσ ε α hα_pos hα_ne_one) := by
  simpa [SubnormalizedState.ConditionalMinEntropyFeasible,
    petzSmoothMinThresholdScale, State.toSubnormalized_identityTensorStateMatrix_eq] using hbound

theorem SubnormalizedState.ConditionalMinEntropyFeasible.of_le_positive_scale
    {ρ' : SubnormalizedState (Prod a b)}
    (σ : State b) {lambda : ℝ} (hlambda : 0 < lambda)
    (hbound :
      ρ'.matrix ≤
        ((lambda : ℝ) : ℂ) • identityTensorStateMatrix (a := a) σ) :
    SubnormalizedState.ConditionalMinEntropyFeasible (a := a) ρ' σ.toSubnormalized
      (-log2 lambda) := by
  have hscale : Real.rpow 2 (-(-log2 lambda)) = lambda := by
    simpa using rpow_two_log2_pos hlambda
  rw [SubnormalizedState.ConditionalMinEntropyFeasible,
    State.toSubnormalized_identityTensorStateMatrix_eq]
  rw [hscale]
  exact hbound

/-- Petz-shaped fixed-reference smooth-min lower bound from a subnormalized
smoothed witness and a direct fixed-reference operator bound.

This is the narrow bridge needed by threshold-compressed substates: the witness
is not normalized, and the smoothing ball is centered at `ρ.toSubnormalized`. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_petz_operator_bound
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (_hα_le_two : α ≤ 2)
    (ρ' : SubnormalizedState (Prod a b))
    (hball : ρ.toSubnormalized.purifiedBall ε ρ')
    (hbound :
      ρ'.matrix ≤
        ((ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) : ℝ) : ℂ) •
          identityTensorStateMatrix (a := a) σ) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  exact le_smoothConditionalMinEntropyFixedSubnormalized_of_feasible_witness
    (a := a) (ρ := ρ) (ρ' := ρ') (σ := σ.toSubnormalized)
    hε_pos.le hε_lt hball
    (SubnormalizedState.ConditionalMinEntropyFeasible.of_le_petzSmoothMinThresholdScale
      (a := a) (ρ' := ρ') ρ hρ σ hσ ε α
      (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) hbound)
    le_rfl

/-- Fixed-reference smooth-min lower bound from an explicit positive threshold
scale, with no full-rank assumption on the left state. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_positive_operator_bound
    (ρ : State (Prod a b)) (σ : State b)
    (ε lambda : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) (hlambda : 0 < lambda)
    (ρ' : SubnormalizedState (Prod a b))
    (hball : ρ.toSubnormalized.purifiedBall ε ρ')
    (hbound :
      ρ'.matrix ≤
        ((lambda : ℝ) : ℂ) • identityTensorStateMatrix (a := a) σ) :
    -log2 lambda ≤
      ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  exact le_smoothConditionalMinEntropyFixedSubnormalized_of_feasible_witness
    (a := a) (ρ := ρ) (ρ' := ρ') (σ := σ.toSubnormalized)
    hε_pos.le hε_lt hball
    (SubnormalizedState.ConditionalMinEntropyFeasible.of_le_positive_scale
      (a := a) (ρ' := ρ') σ hlambda hbound)
    le_rfl

/-! ### Source-shaped smooth-min Petz witness bridge -/

/-- The positive part `Δ = {ρ_AB - λ(I_A ⊗ σ_B)}_+` used in the
source-shaped TCR smooth-min witness. -/
def fixedPetzThresholdPositivePart
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) : CMatrix (Prod a b) :=
  (ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ)⁺

theorem fixedPetzThresholdPositivePart_posSemidef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdPositivePart σ lambda).PosSemidef := by
  unfold fixedPetzThresholdPositivePart
  exact Matrix.nonneg_iff_posSemidef.mp
    (CFC.posPart_nonneg (ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ))

/-- The source-shaped threshold matrix
`Λ = λ(I_A ⊗ σ_B)` for the fixed-reference smooth-min witness. -/
def fixedPetzSmoothMinLambdaMatrix
    (_ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) : CMatrix (Prod a b) :=
  lambda • identityTensorStateMatrix (a := a) σ

/-- Positive-part decomposition gives the source majorization
`ρ_AB ≤ Λ + Δ`. -/
theorem fixedPetzSmoothMin_state_le_lambda_add_delta
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ρ.matrix ≤
      ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
        ρ.fixedPetzThresholdPositivePart σ lambda := by
  let Λ : CMatrix (Prod a b) := ρ.fixedPetzSmoothMinLambdaMatrix σ lambda
  let H : CMatrix (Prod a b) := ρ.matrix - Λ
  have hH : H.IsHermitian := by
    dsimp [H, Λ, fixedPetzSmoothMinLambdaMatrix, identityTensorStateMatrix]
    exact ρ.pos.isHermitian.sub
      ((identityTensorStateMatrix_posSemidef_of_state (a := a) σ).isHermitian.smul
        (IsSelfAdjoint.all lambda))
  rw [Matrix.le_iff]
  have hsub : H⁺ - H = H⁻ := by
    have h := CFC.posPart_sub_negPart H hH.isSelfAdjoint
    calc
      H⁺ - H = H⁺ - (H⁺ - H⁻) := by rw [h]
      _ = H⁻ := by abel
  have hdiff :
      ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
          ρ.fixedPetzThresholdPositivePart σ lambda - ρ.matrix =
        H⁺ - H := by
    simp [H, Λ, fixedPetzSmoothMinLambdaMatrix, fixedPetzThresholdPositivePart]
    abel
  rw [hdiff, hsub]
  exact Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H)

/-- For a positive-definite finite matrix, the CFC inverse square-root is an
ordinary two-sided inverse square-root. -/
theorem cMatrix_rpow_neg_half_mul_self_mul_rpow_neg_half_of_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CMatrix ι} (hA : A.PosDef) :
    CFC.rpow A (-(1 / 2 : ℝ)) * A * CFC.rpow A (-(1 / 2 : ℝ)) = 1 := by
  classical
  let U : CMatrix ι := hA.isHermitian.eigenvectorUnitary
  let D : CMatrix ι :=
    Matrix.diagonal (fun i => ((hA.isHermitian.eigenvalues i : ℝ) : ℂ))
  let R : CMatrix ι :=
    Matrix.diagonal
      (fun i => ((hA.isHermitian.eigenvalues i ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
  have hA_spec : A = U * D * star U := by
    simpa [U, D, Function.comp_def, Unitary.conjStarAlgAut_apply]
      using hA.isHermitian.spectral_theorem
  have hR :
      CFC.rpow A (-(1 / 2 : ℝ)) = U * R * star U := by
    simpa [U, R] using
      cMatrix_rpow_eq_eigenbasis_diagonal hA.posSemidef (-(1 / 2 : ℝ))
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary]
  have hRDR : R * D * R = 1 := by
    dsimp [R, D]
    simp only [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
      have hi : 0 < hA.isHermitian.eigenvalues i := hA.eigenvalues_pos i
      have hreal :
          hA.isHermitian.eigenvalues i ^ (-(1 / 2 : ℝ)) *
              hA.isHermitian.eigenvalues i *
              hA.isHermitian.eigenvalues i ^ (-(1 / 2 : ℝ)) = 1 := by
        have hsum : (-(1 / 2 : ℝ)) + -(1 / 2 : ℝ) = -1 := by ring
        rw [mul_right_comm, ← Real.rpow_add hi, hsum,
          Real.rpow_neg hi.le, Real.rpow_one, inv_mul_cancel₀ (ne_of_gt hi)]
      simpa using (show
        (↑(hA.isHermitian.eigenvalues i ^ (-(1 / 2 : ℝ)) *
          hA.isHermitian.eigenvalues i *
          hA.isHermitian.eigenvalues i ^ (-(1 / 2 : ℝ))) : ℂ) = 1 by
        exact_mod_cast hreal)
    · simp only [Matrix.diagonal_apply_ne _ hij]
      simp [hij]
  calc
    CFC.rpow A (-(1 / 2 : ℝ)) * A * CFC.rpow A (-(1 / 2 : ℝ)) =
        (U * R * star U) * (U * D * star U) * (U * R * star U) := by
      rw [hR, hA_spec]
    _ = U * (R * D * R) * star U := by
      conv_lhs =>
        rw [show U * R * star U * (U * D * star U) * (U * R * star U) =
          U * R * (star U * U) * D * (star U * U) * R * star U by noncomm_ring]
      rw [hU]
      noncomm_ring
    _ = 1 := by
      rw [hRDR]
      simp [U]

theorem cMatrix_rpow_neg_half_mul_self_eq_psdSqrt_of_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CMatrix ι} (hA : A.PosDef) :
    CFC.rpow A (-(1 / 2 : ℝ)) * A = psdSqrt A := by
  calc
    CFC.rpow A (-(1 / 2 : ℝ)) * A =
        CFC.rpow A (-(1 / 2 : ℝ)) * CFC.rpow A 1 := by
      exact congrArg (fun X => CFC.rpow A (-(1 / 2 : ℝ)) * X)
        (CFC.rpow_one A
          (ha := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef)).symm
    _ = CFC.rpow A (-(1 / 2 : ℝ) + 1) := by
      exact (CFC.rpow_add (a := A) (x := -(1 / 2 : ℝ)) (y := 1) hA.isUnit).symm
    _ = CFC.rpow A (1 / 2 : ℝ) := by norm_num
    _ = psdSqrt A := by
      simpa [psdSqrt] using (CFC.sqrt_eq_rpow (a := A)).symm

/-- The source-shaped positive-definite/core filter
`G = Λ^{1/2}(Λ + Δ)^{-1/2}`.

For now this is the ordinary CFC `rpow (-1/2)` version.  Downstream lemmas
keep the inverse/square-root order fact as an explicit hypothesis, so the
support-inverse generalization can replace this definition without changing the
smooth-min handoff. -/
def fixedPetzSmoothMinG
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) : CMatrix (Prod a b) :=
  psdSqrt (ρ.fixedPetzSmoothMinLambdaMatrix σ lambda) *
    CFC.rpow
      (ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
        ρ.fixedPetzThresholdPositivePart σ lambda)
      (-(1 / 2 : ℝ))

/-- Matrix of the source-shaped witness `ρ~ = GρG†`. -/
def fixedPetzSmoothMinWitnessMatrix
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) : CMatrix (Prod a b) :=
  ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix *
    Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda)

theorem fixedPetzSmoothMinLambdaMatrix_posDef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hlambda : 0 < lambda) (hσ : σ.matrix.PosDef) :
    (ρ.fixedPetzSmoothMinLambdaMatrix σ lambda).PosDef := by
  unfold fixedPetzSmoothMinLambdaMatrix
  exact (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ).smul hlambda

theorem fixedPetzSmoothMinLambda_add_delta_posDef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hlambda : 0 < lambda) (hσ : σ.matrix.PosDef) :
    (ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
      ρ.fixedPetzThresholdPositivePart σ lambda).PosDef :=
  by
    rw [add_comm]
    exact Matrix.PosDef.posSemidef_add
      (ρ.fixedPetzThresholdPositivePart_posSemidef σ lambda)
      (ρ.fixedPetzSmoothMinLambdaMatrix_posDef σ lambda hlambda hσ)

theorem fixedPetzSmoothMinG_filter_conj_eq_lambda_posDef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hlambda : 0 < lambda) (hσ : σ.matrix.PosDef) :
    ρ.fixedPetzSmoothMinG σ lambda *
        (ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
          ρ.fixedPetzThresholdPositivePart σ lambda) *
          Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) =
      ρ.fixedPetzSmoothMinLambdaMatrix σ lambda := by
  let Λ : CMatrix (Prod a b) := ρ.fixedPetzSmoothMinLambdaMatrix σ lambda
  let Δ : CMatrix (Prod a b) := ρ.fixedPetzThresholdPositivePart σ lambda
  let A : CMatrix (Prod a b) := Λ + Δ
  let R : CMatrix (Prod a b) := CFC.rpow A (-(1 / 2 : ℝ))
  let S : CMatrix (Prod a b) := psdSqrt Λ
  have hΛpsd : Λ.PosSemidef := by
    simpa [Λ] using
      (ρ.fixedPetzSmoothMinLambdaMatrix_posDef σ lambda hlambda hσ).posSemidef
  have hApos : A.PosDef := by
    simpa [A, Λ, Δ] using
      ρ.fixedPetzSmoothMinLambda_add_delta_posDef σ lambda hlambda hσ
  have hR_sandwich : R * A * R = 1 := by
    simpa [R, A] using
      cMatrix_rpow_neg_half_mul_self_mul_rpow_neg_half_of_posDef hApos
  have hS2 : S * S = Λ := by
    simpa [S, Λ] using psdSqrt_mul_self_of_posSemidef hΛpsd
  have hS_star : Matrix.conjTranspose S = S := by
    simpa [S, Matrix.star_eq_conjTranspose] using (psdSqrt_isHermitian Λ).eq
  have hR_star : Matrix.conjTranspose R = R := by
    have hRpsd : R.PosSemidef := by
      simpa [R, A] using cMatrix_rpow_posSemidef (s := (-(1 / 2 : ℝ))) hApos.posSemidef
    simpa [R, Matrix.star_eq_conjTranspose] using hRpsd.isHermitian.eq
  calc
    ρ.fixedPetzSmoothMinG σ lambda *
        (ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
          ρ.fixedPetzThresholdPositivePart σ lambda) *
          Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) =
        (S * R) * A * Matrix.conjTranspose (S * R) := by
      simp [fixedPetzSmoothMinG, S, R, A, Λ, Δ]
    _ = S * (R * A * R) * S := by
      rw [Matrix.conjTranspose_mul, hS_star, hR_star]
      noncomm_ring
    _ = Λ := by
      rw [hR_sandwich]
      simp [hS2]

theorem fixedPetzSmoothMinG_filter_conj_le_lambda_posDef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hlambda : 0 < lambda) (hσ : σ.matrix.PosDef) :
    ρ.fixedPetzSmoothMinG σ lambda *
        (ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
          ρ.fixedPetzThresholdPositivePart σ lambda) *
          Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) ≤
      ρ.fixedPetzSmoothMinLambdaMatrix σ lambda := by
  rw [ρ.fixedPetzSmoothMinG_filter_conj_eq_lambda_posDef σ lambda hlambda hσ]

theorem fixedPetzSmoothMinWitnessMatrix_posSemidef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzSmoothMinWitnessMatrix σ lambda).PosSemidef := by
  unfold fixedPetzSmoothMinWitnessMatrix
  exact ρ.pos.mul_mul_conjTranspose_same (ρ.fixedPetzSmoothMinG σ lambda)

theorem fixedPetzSmoothMinWitnessMatrix_trace_re_le_one_of_contract
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1) :
    (ρ.fixedPetzSmoothMinWitnessMatrix σ lambda).trace.re ≤ 1 := by
  let G : CMatrix (Prod a b) := ρ.fixedPetzSmoothMinG σ lambda
  have htrace_le :
      ((ρ.matrix * (Matrix.conjTranspose G * G)).trace).re ≤
        ((ρ.matrix * 1).trace).re :=
    cMatrix_trace_mul_le_of_le_posSemidef_left ρ.pos hcontract
  have hcyc :
      (ρ.fixedPetzSmoothMinWitnessMatrix σ lambda).trace =
        (ρ.matrix * (Matrix.conjTranspose G * G)).trace := by
    calc
      (ρ.fixedPetzSmoothMinWitnessMatrix σ lambda).trace =
          (G * ρ.matrix * Matrix.conjTranspose G).trace := rfl
      _ = (ρ.matrix * (Matrix.conjTranspose G * G)).trace := by
          calc
            (G * ρ.matrix * Matrix.conjTranspose G).trace =
                ((G * ρ.matrix) * Matrix.conjTranspose G).trace := by
              rw [Matrix.mul_assoc]
            _ = (Matrix.conjTranspose G * (G * ρ.matrix)).trace := by
              rw [Matrix.trace_mul_comm]
            _ = ((Matrix.conjTranspose G * G) * ρ.matrix).trace := by
              rw [← Matrix.mul_assoc]
            _ = (ρ.matrix * (Matrix.conjTranspose G * G)).trace := by
              rw [Matrix.trace_mul_comm]
  rw [hcyc]
  rw [Matrix.mul_one, ρ.trace_eq_one] at htrace_le
  norm_num at htrace_le
  exact htrace_le

/-- The source-shaped witness as a subnormalized state, assuming the filter is
contractive in the `G†G ≤ I` sense. -/
def fixedPetzSmoothMinWitnessSubstate
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1) :
    SubnormalizedState (Prod a b) where
  matrix := ρ.fixedPetzSmoothMinWitnessMatrix σ lambda
  pos := ρ.fixedPetzSmoothMinWitnessMatrix_posSemidef σ lambda
  trace_le_one :=
    ρ.fixedPetzSmoothMinWitnessMatrix_trace_re_le_one_of_contract σ lambda hcontract

@[simp]
theorem fixedPetzSmoothMinWitnessSubstate_matrix
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1) :
    (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract).matrix =
      ρ.fixedPetzSmoothMinWitnessMatrix σ lambda :=
  rfl

/-- Conjugating an operator inequality by a fixed matrix preserves the order. -/
theorem cMatrix_conj_le_conj_of_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R X G : CMatrix ι} (hRX : R ≤ X) :
    G * R * Matrix.conjTranspose G ≤ G * X * Matrix.conjTranspose G := by
  rw [Matrix.le_iff] at hRX ⊢
  have hpsd := hRX.mul_mul_conjTranspose_same G
  have hdiff :
      G * X * Matrix.conjTranspose G - G * R * Matrix.conjTranspose G =
        G * (X - R) * Matrix.conjTranspose G := by
    noncomm_ring
  rwa [hdiff]

theorem fixedPetzSmoothMinG_contract_posDef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hlambda : 0 < lambda) (hσ : σ.matrix.PosDef) :
    Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
        ρ.fixedPetzSmoothMinG σ lambda ≤ 1 := by
  let Λ : CMatrix (Prod a b) := ρ.fixedPetzSmoothMinLambdaMatrix σ lambda
  let Δ : CMatrix (Prod a b) := ρ.fixedPetzThresholdPositivePart σ lambda
  let A : CMatrix (Prod a b) := Λ + Δ
  let R : CMatrix (Prod a b) := CFC.rpow A (-(1 / 2 : ℝ))
  let S : CMatrix (Prod a b) := psdSqrt Λ
  have hΛpsd : Λ.PosSemidef := by
    simpa [Λ] using
      (ρ.fixedPetzSmoothMinLambdaMatrix_posDef σ lambda hlambda hσ).posSemidef
  have hΔpsd : Δ.PosSemidef := by
    simpa [Δ] using ρ.fixedPetzThresholdPositivePart_posSemidef σ lambda
  have hApos : A.PosDef := by
    simpa [A, Λ, Δ] using
      ρ.fixedPetzSmoothMinLambda_add_delta_posDef σ lambda hlambda hσ
  have hΛ_le_A : Λ ≤ A := by
    rw [Matrix.le_iff]
    simpa [A] using hΔpsd
  have hR_sandwich : R * A * R = 1 := by
    simpa [R, A] using
      cMatrix_rpow_neg_half_mul_self_mul_rpow_neg_half_of_posDef hApos
  have hS2 : S * S = Λ := by
    simpa [S, Λ] using psdSqrt_mul_self_of_posSemidef hΛpsd
  have hS_star : Matrix.conjTranspose S = S := by
    simpa [S, Matrix.star_eq_conjTranspose] using (psdSqrt_isHermitian Λ).eq
  have hR_star : Matrix.conjTranspose R = R := by
    have hRpsd : R.PosSemidef := by
      simpa [R, A] using cMatrix_rpow_posSemidef (s := (-(1 / 2 : ℝ))) hApos.posSemidef
    simpa [R, Matrix.star_eq_conjTranspose] using hRpsd.isHermitian.eq
  have hconj : R * Λ * R ≤ R * A * R := by
    simpa [hR_star] using cMatrix_conj_le_conj_of_le (G := R) hΛ_le_A
  have hG_eq : ρ.fixedPetzSmoothMinG σ lambda = S * R := by
    simp [fixedPetzSmoothMinG, S, R, A, Λ, Δ]
  calc
    Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
        ρ.fixedPetzSmoothMinG σ lambda =
        R * Λ * R := by
      rw [hG_eq, Matrix.conjTranspose_mul, hS_star, hR_star]
      calc
        R * S * (S * R) = R * (S * S) * R := by noncomm_ring
        _ = R * Λ * R := by rw [hS2]
    _ ≤ R * A * R := hconj
    _ = 1 := hR_sandwich

private theorem contract_doubled_effect_posSemidef_of_contract
    {ι : Type*} [Fintype ι] [DecidableEq ι] {G : CMatrix ι}
    (hcontract : Matrix.conjTranspose G * G ≤ 1) :
    ((1 : CMatrix ι) + 1 - (G + Matrix.conjTranspose G)).PosSemidef := by
  have hdiff : ((1 : CMatrix ι) - Matrix.conjTranspose G * G).PosSemidef := by
    simpa [Matrix.le_iff] using hcontract
  have hsq :
      (((1 : CMatrix ι) - Matrix.conjTranspose G) *
          ((1 : CMatrix ι) - G)).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self ((1 : CMatrix ι) - G)
    simpa [Matrix.conjTranspose_sub] using h
  have hsum := Matrix.PosSemidef.add hsq hdiff
  convert hsum using 1
  noncomm_ring

/-- TCR source trace estimate for the `GρG†` smooth-min witness:
the trace loss of the source filter is controlled by the threshold positive
part `Δ = {ρ_AB - λ(I_A ⊗ σ_B)}_+`. -/
theorem fixedPetzSmoothMinG_trace_loss_le_positivePart_trace
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hlambda : 0 < lambda) (hσ : σ.matrix.PosDef) :
    1 - (((ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace).re) ≤
      (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re := by
  let Λ : CMatrix (Prod a b) := ρ.fixedPetzSmoothMinLambdaMatrix σ lambda
  let Δ : CMatrix (Prod a b) := ρ.fixedPetzThresholdPositivePart σ lambda
  let A : CMatrix (Prod a b) := Λ + Δ
  let G : CMatrix (Prod a b) := ρ.fixedPetzSmoothMinG σ lambda
  let E : CMatrix (Prod a b) := (1 : CMatrix (Prod a b)) + 1 -
    (G + Matrix.conjTranspose G)
  let S : CMatrix (Prod a b) := psdSqrt Λ
  let R : CMatrix (Prod a b) := CFC.rpow A (-(1 / 2 : ℝ))
  have hcontract : Matrix.conjTranspose G * G ≤ 1 := by
    simpa [G] using ρ.fixedPetzSmoothMinG_contract_posDef σ lambda hlambda hσ
  have hEpos : E.PosSemidef := by
    simpa [E, G] using
      contract_doubled_effect_posSemidef_of_contract (G := G) hcontract
  have hρ_le_A : ρ.matrix ≤ A := by
    simpa [A, Λ, Δ] using ρ.fixedPetzSmoothMin_state_le_lambda_add_delta σ lambda
  have htrace_le : ((E * ρ.matrix).trace).re ≤ ((E * A).trace).re :=
    cMatrix_trace_mul_le_of_le_posSemidef_left hEpos hρ_le_A
  have hGρ_conj :
      ((Matrix.conjTranspose G * ρ.matrix).trace).re =
        ((G * ρ.matrix).trace).re :=
    trace_conjTranspose_mul_hermitian_re_eq ρ.pos.isHermitian
  have hEρ :
      ((E * ρ.matrix).trace).re =
        2 * (1 - ((G * ρ.matrix).trace).re) := by
    simp [E, Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub,
      hGρ_conj, ρ.trace_eq_one]
    ring
  have hΛpsd : Λ.PosSemidef := by
    simpa [Λ] using
      (ρ.fixedPetzSmoothMinLambdaMatrix_posDef σ lambda hlambda hσ).posSemidef
  have hΔpsd : Δ.PosSemidef := by
    simpa [Δ] using ρ.fixedPetzThresholdPositivePart_posSemidef σ lambda
  have hApos : A.PosDef := by
    simpa [A, Λ, Δ] using
      ρ.fixedPetzSmoothMinLambda_add_delta_posDef σ lambda hlambda hσ
  have hΛ_le_A : Λ ≤ A := by
    rw [Matrix.le_iff]
    simpa [A] using hΔpsd
  have hSpos : S.PosSemidef := by
    simpa [S] using psdSqrt_pos Λ
  have hS2 : S * S = Λ := by
    simpa [S, Λ] using psdSqrt_mul_self_of_posSemidef hΛpsd
  have hS_le_sqrtA : S ≤ psdSqrt A := by
    simpa [S] using psdSqrt_le_psdSqrt_of_le hΛ_le_A
  have htrace_S : Λ.trace.re ≤ ((S * psdSqrt A).trace).re := by
    have h := cMatrix_trace_mul_le_of_le_posSemidef_left hSpos hS_le_sqrtA
    simpa [hS2] using h
  have hG_eq : G = S * R := by
    simp [G, S, R, A, Λ, Δ, fixedPetzSmoothMinG]
  have hRA : R * A = psdSqrt A := by
    simpa [R, A] using cMatrix_rpow_neg_half_mul_self_eq_psdSqrt_of_posDef hApos
  have hGA : G * A = S * psdSqrt A := by
    rw [hG_eq]
    calc
      (S * R) * A = S * (R * A) := by noncomm_ring
      _ = S * psdSqrt A := by rw [hRA]
  have hGA_lower : Λ.trace.re ≤ ((G * A).trace).re := by
    rw [hGA]
    exact htrace_S
  have hGA_conj :
      ((Matrix.conjTranspose G * A).trace).re = ((G * A).trace).re :=
    trace_conjTranspose_mul_hermitian_re_eq hApos.isHermitian
  have hAtr : A.trace.re = Λ.trace.re + Δ.trace.re := by
    simp [A, Matrix.trace_add]
  have hEA :
      ((E * A).trace).re ≤ 2 * Δ.trace.re := by
    have hEAeq :
        ((E * A).trace).re =
          2 * A.trace.re - ((G * A).trace).re -
            ((Matrix.conjTranspose G * A).trace).re := by
      simp [E, Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub,
        ]
      ring
    rw [hEAeq, hGA_conj, hAtr]
    linarith
  have htwice :
      2 * (1 - ((G * ρ.matrix).trace).re) ≤ 2 * Δ.trace.re := by
    rw [← hEρ]
    exact le_trans htrace_le hEA
  have hloss : 1 - ((G * ρ.matrix).trace).re ≤ Δ.trace.re := by
    linarith
  simpa [G, Δ] using hloss

/-- If `ρ ≤ Λ + Δ`, then the source filter reduces the witness bound to the
single CFC inverse/square-root inequality `G(Λ+Δ)G† ≤ Λ`. -/
theorem fixedPetzSmoothMinWitnessMatrix_le_lambda_of_le_add_delta
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hρ_le :
      ρ.matrix ≤
        ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
          ρ.fixedPetzThresholdPositivePart σ lambda)
    (hconj :
      ρ.fixedPetzSmoothMinG σ lambda *
          (ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
            ρ.fixedPetzThresholdPositivePart σ lambda) *
            Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) ≤
        ρ.fixedPetzSmoothMinLambdaMatrix σ lambda) :
    ρ.fixedPetzSmoothMinWitnessMatrix σ lambda ≤
      ρ.fixedPetzSmoothMinLambdaMatrix σ lambda := by
  exact le_trans (cMatrix_conj_le_conj_of_le
    (G := ρ.fixedPetzSmoothMinG σ lambda) hρ_le) hconj

/-- Source-shaped witness bound reduced only to the CFC filter inequality
`G(Λ+Δ)G† ≤ Λ`; the positive-part majorization is discharged here. -/
theorem fixedPetzSmoothMinWitnessMatrix_le_lambda_of_filter_conj
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hconj :
      ρ.fixedPetzSmoothMinG σ lambda *
          (ρ.fixedPetzSmoothMinLambdaMatrix σ lambda +
            ρ.fixedPetzThresholdPositivePart σ lambda) *
            Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) ≤
        ρ.fixedPetzSmoothMinLambdaMatrix σ lambda) :
    ρ.fixedPetzSmoothMinWitnessMatrix σ lambda ≤
      ρ.fixedPetzSmoothMinLambdaMatrix σ lambda :=
  ρ.fixedPetzSmoothMinWitnessMatrix_le_lambda_of_le_add_delta σ lambda
    (ρ.fixedPetzSmoothMin_state_le_lambda_add_delta σ lambda) hconj

/-- Source-shaped `GρG†` handoff at an explicit positive threshold scale.
This is the PSD-left version of the threshold bridge: the center state is an
arbitrary finite state, while full-rankness is only required for the fixed
reference when the concrete TCR filter is used. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_bound_scale
    (ρ : State (Prod a b)) (σ : State b)
    (ε lambda : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) (hlambda : 0 < lambda)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1)
    (hball :
      ρ.toSubnormalized.purifiedBall ε
        (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract))
    (hbound :
      (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract).matrix ≤
        ((lambda : ℝ) : ℂ) • identityTensorStateMatrix (a := a) σ) :
    -log2 lambda ≤
      ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  exact smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_positive_operator_bound
    (ρ := ρ) (σ := σ) ε lambda hε_pos hε_lt hlambda
    (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract) hball hbound

/-- Source-shaped `GρG†` handoff at an explicit positive threshold scale, with
the CFC filter order inequality discharged from a full-rank reference. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_ball_scale
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε lambda : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) (hlambda : 0 < lambda)
    (hball :
      ρ.toSubnormalized.purifiedBall ε
        (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda
          (ρ.fixedPetzSmoothMinG_contract_posDef σ lambda hlambda hσ))) :
    -log2 lambda ≤
      ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1 :=
    ρ.fixedPetzSmoothMinG_contract_posDef σ lambda hlambda hσ
  have hbound :
      (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract).matrix ≤
        ((lambda : ℝ) : ℂ) • identityTensorStateMatrix (a := a) σ := by
    have hmain :
        ρ.fixedPetzSmoothMinWitnessMatrix σ lambda ≤
          ρ.fixedPetzSmoothMinLambdaMatrix σ lambda :=
      ρ.fixedPetzSmoothMinWitnessMatrix_le_lambda_of_filter_conj σ lambda
        (ρ.fixedPetzSmoothMinG_filter_conj_le_lambda_posDef σ lambda hlambda hσ)
    simpa [fixedPetzSmoothMinWitnessSubstate_matrix,
      fixedPetzSmoothMinLambdaMatrix] using hmain
  exact
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_bound_scale
      σ ε lambda hε_pos hε_lt hlambda hcontract
      (by simpa [hcontract] using hball) hbound

/-- Source-shaped `GρG†` handoff into the existing subnormalized smooth-min
lower-bound theorem.  The two remaining source obligations are explicit:
the witness must lie in the purified ball, and the CFC filter must satisfy the
direct threshold operator bound. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_bound
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hcontract :
      Matrix.conjTranspose
          (ρ.fixedPetzSmoothMinG σ
            (ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
              (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm))) *
          ρ.fixedPetzSmoothMinG σ
            (ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
              (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)) ≤ 1)
    (hball :
      ρ.toSubnormalized.purifiedBall ε
        (ρ.fixedPetzSmoothMinWitnessSubstate σ
          (ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
            (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm))
          hcontract))
    (hbound :
      (ρ.fixedPetzSmoothMinWitnessSubstate σ
        (ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm))
        hcontract).matrix ≤
        ((ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) : ℝ) : ℂ) •
          identityTensorStateMatrix (a := a) σ) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  exact smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_petz_operator_bound
    (ρ := ρ) hρ (σ := σ) hσ ε α hε_pos hε_lt hα_gt hα_le_two
    (ρ.fixedPetzSmoothMinWitnessSubstate σ
      (ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm))
      hcontract)
    hball hbound

/-- Source-shaped `GρG†` smooth-min handoff with the contractivity and
operator-order parts discharged in the positive-definite core.  The only
remaining source obligation is the purified-ball estimate for the TCR witness. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_ball
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hball :
      ρ.toSubnormalized.purifiedBall ε
        (ρ.fixedPetzSmoothMinWitnessSubstate σ
          (ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
            (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm))
          (ρ.fixedPetzSmoothMinG_contract_posDef σ
            (ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
              (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm))
            (ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α
              (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm))
            hσ))) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let lam : ℝ :=
    ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
      (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
  let hlam : 0 < lam :=
    ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α
      (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
  let hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lam) *
          ρ.fixedPetzSmoothMinG σ lam ≤ 1 :=
    ρ.fixedPetzSmoothMinG_contract_posDef σ lam hlam hσ
  have hbound :
      (ρ.fixedPetzSmoothMinWitnessSubstate σ lam hcontract).matrix ≤
        ((lam : ℝ) : ℂ) • identityTensorStateMatrix (a := a) σ := by
    have hmain :
        ρ.fixedPetzSmoothMinWitnessMatrix σ lam ≤
          ρ.fixedPetzSmoothMinLambdaMatrix σ lam :=
      ρ.fixedPetzSmoothMinWitnessMatrix_le_lambda_of_filter_conj σ lam
        (ρ.fixedPetzSmoothMinG_filter_conj_le_lambda_posDef σ lam hlam hσ)
    simpa [fixedPetzSmoothMinWitnessSubstate_matrix,
      fixedPetzSmoothMinLambdaMatrix] using hmain
  exact smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_bound
    (ρ := ρ) hρ (σ := σ) hσ ε α hε_pos hε_lt hα_gt hα_le_two
    hcontract (by simpa [lam, hcontract] using hball) hbound

end State

end

end QIT
