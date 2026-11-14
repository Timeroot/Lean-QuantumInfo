/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.RenyiDPI.TraceLogBridge
public import QIT.Information.Renyi.SandwichedRenyiOptimizedUSC
public import QIT.States.PosSqrtOrder

/-!
# Reference order for sandwiched Renyi divergence

This module proves the reference-order property used in Tomamichel's direct
proof of conditional sandwiched-Renyi monotonicity.  If `sigma <= tau`, then
the divergence is antitone in its reference:

`D_tilde_alpha(rho || tau) <= D_tilde_alpha(rho || sigma)`.

The proof follows the source power-order route.  The sandwiched power trace is
first rewritten in the alternate form
`rho^(1/2) sigma^((1-alpha)/alpha) rho^(1/2)`.  Positive reference powers are
operator monotone below one; negative powers are operator antitone above one.
Singular high-order references are obtained from positive regularization, and
the Umegaki endpoint is the right limit as `alpha -> 1+`.

Tomamichel2015FiniteResources, `renyi.tex:119-124`, property X;
`renyi.tex:552-575`, Lemma `lm:pinch2a`; and `renyi.tex:679-703`, the
support-aware `alpha -> 1` endpoint.
-/

@[expose] public section

open Filter
open scoped ComplexOrder MatrixOrder Topology Matrix.Norms.L2Operator

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

noncomputable local instance instCMatrixCStarAlgebraForReferenceOrder
    (n : Type u) [Fintype n] [DecidableEq n] : CStarAlgebra (CMatrix n) := {}

namespace State

/-- Alternate reference-order matrix for the sandwiched power trace. -/
def sandwichedRenyiReferenceOuter
    (rho : State a) (sigma : CMatrix a) (alpha : Real) : CMatrix a :=
  rho.sqrtMatrix * CFC.rpow sigma ((1 - alpha) / alpha) * rho.sqrtMatrix

theorem sandwichedRenyiReferenceOuter_posSemidef
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosSemidef)
    (alpha : Real) :
    (sandwichedRenyiReferenceOuter rho sigma alpha).PosSemidef := by
  have hpow : (CFC.rpow sigma ((1 - alpha) / alpha)).PosSemidef :=
    cMatrix_rpow_posSemidef hsigma
  simpa [sandwichedRenyiReferenceOuter, rho.sqrtMatrix_isHermitian.eq] using
    hpow.mul_mul_conjTranspose_same rho.sqrtMatrix

/-- The source alternate expression for the sandwiched power trace. -/
theorem sandwichedRenyiReferenceInner_psdTracePower_eq_outer
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosSemidef)
    {alpha : Real} (halpha_pos : 0 < alpha) (halpha_ne_one : alpha ≠ 1) :
    psdTracePower (sandwichedRenyiReferenceInner rho sigma alpha)
        (sandwichedRenyiReferenceInner_posSemidef rho hsigma alpha) alpha =
      psdTracePower (sandwichedRenyiReferenceOuter rho sigma alpha)
        (sandwichedRenyiReferenceOuter_posSemidef rho hsigma alpha) alpha := by
  let s : Real := (1 - alpha) / (2 * alpha)
  have hs_ne : s ≠ 0 := by
    dsimp [s]
    exact div_ne_zero (sub_ne_zero.mpr halpha_ne_one.symm)
      (mul_ne_zero (by norm_num) halpha_pos.ne')
  have htwo_s : 2 * s = (1 - alpha) / alpha := by
    dsimp [s]
    field_simp [halpha_pos.ne']
  have hsqrt : CFC.rpow rho.matrix (1 / 2 : Real) = rho.sqrtMatrix := by
    simp [State.sqrtMatrix, psdSqrt, CFC.sqrt_eq_rpow]
  unfold psdTracePower
  simpa only [sandwichedRenyiReferenceInner,
      sandwichedRenyiReferenceOuter, hsqrt, htwo_s] using
    sandwichedRenyiInner_trace_re_congruence rho.pos hsigma hs_ne halpha_pos

/-- The alternate expression preserves the PSD Schatten expression. -/
theorem sandwichedRenyiReferenceInner_psdSchattenPNorm_eq_outer
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosSemidef)
    {alpha : Real} (halpha_pos : 0 < alpha) (halpha_ne_one : alpha ≠ 1) :
    psdSchattenPNorm (sandwichedRenyiReferenceInner rho sigma alpha)
        (sandwichedRenyiReferenceInner_posSemidef rho hsigma alpha)
        ⟨alpha, halpha_pos⟩ =
      psdSchattenPNorm (sandwichedRenyiReferenceOuter rho sigma alpha)
        (sandwichedRenyiReferenceOuter_posSemidef rho hsigma alpha)
        ⟨alpha, halpha_pos⟩ := by
  unfold psdSchattenPNorm Internal.psdSchattenExpression
  rw [sandwichedRenyiReferenceInner_psdTracePower_eq_outer rho hsigma
    halpha_pos halpha_ne_one]

/-- Congruence by `rho^(1/2)` preserves reference-power order. -/
theorem sandwichedRenyiReferenceOuter_le_of_rpow_le
    (rho : State a) {sigma tau : CMatrix a} {alpha : Real}
    (hpow : CFC.rpow sigma ((1 - alpha) / alpha) <=
      CFC.rpow tau ((1 - alpha) / alpha)) :
    sandwichedRenyiReferenceOuter rho sigma alpha <=
      sandwichedRenyiReferenceOuter rho tau alpha := by
  rw [Matrix.le_iff]
  have hdiff :
      (CFC.rpow tau ((1 - alpha) / alpha) -
        CFC.rpow sigma ((1 - alpha) / alpha)).PosSemidef :=
    Matrix.le_iff.mp hpow
  have hcongr := hdiff.mul_mul_conjTranspose_same rho.sqrtMatrix
  simpa [sandwichedRenyiReferenceOuter, rho.sqrtMatrix_isHermitian.eq,
    Matrix.mul_sub, Matrix.sub_mul] using hcongr

/-- In the low-order source range, the positive-power `Q` functional is
monotone in the PSD reference. -/
theorem sandwichedRenyiQ_mono_reference_of_half_le_lt_one
    (rho : State a) {sigma tau : CMatrix a}
    (hsigma : sigma.PosSemidef) (htau : tau.PosSemidef)
    (hsigma_tau : sigma <= tau) {alpha : Real}
    (halpha_half : 1 / 2 <= alpha) (halpha_lt_one : alpha < 1) :
    sandwichedRenyiQ rho.matrix sigma rho.pos hsigma alpha <=
      sandwichedRenyiQ rho.matrix tau rho.pos htau alpha := by
  have halpha_pos : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha_half
  have halpha_ne_one : alpha ≠ 1 := ne_of_lt halpha_lt_one
  have hexp_nonneg : 0 <= (1 - alpha) / alpha :=
    div_nonneg (sub_nonneg.mpr halpha_lt_one.le) halpha_pos.le
  have hexp_le_one : (1 - alpha) / alpha <= 1 := by
    apply (div_le_one halpha_pos).2
    linarith
  have hpow : CFC.rpow sigma ((1 - alpha) / alpha) <=
      CFC.rpow tau ((1 - alpha) / alpha) :=
    CFC.rpow_le_rpow (Set.mem_Icc.mpr <| And.intro hexp_nonneg hexp_le_one)
      hsigma_tau
  have houter := sandwichedRenyiReferenceOuter_le_of_rpow_le rho hpow
  have htracePower :
      psdTracePower (sandwichedRenyiReferenceOuter rho sigma alpha)
          (sandwichedRenyiReferenceOuter_posSemidef rho hsigma alpha) alpha <=
        psdTracePower (sandwichedRenyiReferenceOuter rho tau alpha)
          (sandwichedRenyiReferenceOuter_posSemidef rho htau alpha) alpha := by
    have houterPow :
        CFC.rpow (sandwichedRenyiReferenceOuter rho sigma alpha) alpha <=
          CFC.rpow (sandwichedRenyiReferenceOuter rho tau alpha) alpha :=
      CFC.rpow_le_rpow
        (Set.mem_Icc.mpr <| And.intro halpha_pos.le halpha_lt_one.le) houter
    simpa [psdTracePower] using
      cMatrix_trace_mul_le_of_le_posSemidef_right
        (A := CFC.rpow (sandwichedRenyiReferenceOuter rho sigma alpha) alpha)
        (B := CFC.rpow (sandwichedRenyiReferenceOuter rho tau alpha) alpha)
        Matrix.PosSemidef.one houterPow
  change
    psdTracePower (sandwichedRenyiReferenceInner rho sigma alpha)
        (sandwichedRenyiReferenceInner_posSemidef rho hsigma alpha) alpha <=
      psdTracePower (sandwichedRenyiReferenceInner rho tau alpha)
        (sandwichedRenyiReferenceInner_posSemidef rho htau alpha) alpha
  rw [sandwichedRenyiReferenceInner_psdTracePower_eq_outer rho hsigma
      halpha_pos halpha_ne_one,
    sandwichedRenyiReferenceInner_psdTracePower_eq_outer rho htau
      halpha_pos halpha_ne_one]
  exact htracePower

/-- Extended-real low-order sandwiched Renyi divergence is antitone in its PSD
reference.  The zero-`Q` branch is handled by the source value `+infinity`. -/
theorem sandwichedRenyiPSDReferenceLowAlphaE_antitone_reference
    (rho : State a) {sigma tau : CMatrix a}
    (hsigma : sigma.PosSemidef) (htau : tau.PosSemidef)
    (hsigma_tau : sigma <= tau) {alpha : Real}
    (halpha_half : 1 / 2 <= alpha) (halpha_lt_one : alpha < 1) :
    sandwichedRenyiPSDReferenceLowAlphaE rho tau htau alpha <=
      sandwichedRenyiPSDReferenceLowAlphaE rho sigma hsigma alpha := by
  have hQle := sandwichedRenyiQ_mono_reference_of_half_le_lt_one rho
    hsigma htau hsigma_tau halpha_half halpha_lt_one
  by_cases hQsigma_zero :
      sandwichedRenyiQ rho.matrix sigma rho.pos hsigma alpha = 0
  · rw [sandwichedRenyiPSDReferenceLowAlphaE_eq_top_of_Q_eq_zero
      rho hsigma alpha hQsigma_zero]
    exact le_top
  · have hQsigma_pos :
        0 < sandwichedRenyiQ rho.matrix sigma rho.pos hsigma alpha :=
      sandwichedRenyiQ_pos_of_ne_zero rho.pos hsigma alpha hQsigma_zero
    have hQtau_pos :
        0 < sandwichedRenyiQ rho.matrix tau rho.pos htau alpha :=
      lt_of_lt_of_le hQsigma_pos hQle
    have hQtau_ne :
        sandwichedRenyiQ rho.matrix tau rho.pos htau alpha ≠ 0 :=
      ne_of_gt hQtau_pos
    rw [sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero
        rho htau alpha hQtau_ne,
      sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero
        rho hsigma alpha hQsigma_zero]
    apply EReal.coe_le_coe_iff.mpr
    unfold sandwichedRenyiPSDReferenceLowAlpha
    have hlog :
        log2 (sandwichedRenyiQ rho.matrix sigma rho.pos hsigma alpha) <=
          log2 (sandwichedRenyiQ rho.matrix tau rho.pos htau alpha) := by
      unfold log2
      exact div_le_div_of_nonneg_right
        (Real.log_le_log hQsigma_pos hQle)
        (le_of_lt <| Real.log_pos one_lt_two)
    exact mul_le_mul_of_nonpos_left hlog
      (le_of_lt <| one_div_neg.mpr <| sub_neg.mpr halpha_lt_one)

/-- Support inclusion is monotone when a PSD reference is enlarged in Loewner
order. -/
theorem supports_of_supports_of_reference_le
    (rho : State a) {sigma tau : CMatrix a}
    (hsigma : sigma.PosSemidef) (hsigma_tau : sigma <= tau)
    (hSupport : Matrix.Supports rho.matrix sigma) :
    Matrix.Supports rho.matrix tau := by
  have hdiff : (tau - sigma).PosSemidef := Matrix.le_iff.mp hsigma_tau
  have hsigma_support_tau : Matrix.Supports sigma tau := by
    have htau : tau = sigma + (tau - sigma) := by abel
    rw [htau]
    exact Matrix.Supports.left_of_posSemidef_add hsigma hdiff
  exact hSupport.trans hsigma_support_tau

/-- Positive-definite high-order finite branches are antitone in the
reference.  This is the negative-power half of the source proof. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_antitone_reference_of_posDef
    (rho : State a) {sigma tau : CMatrix a}
    (hsigma : sigma.PosDef) (htau : tau.PosDef)
    (hsigma_tau : sigma <= tau) {alpha : Real} (halpha : 1 < alpha) :
    sandwichedRenyiPSDReferenceHighAlphaFinite rho tau htau.posSemidef alpha <=
      sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma.posSemidef alpha := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have halpha_ne_one : alpha ≠ 1 := ne_of_gt halpha
  let t : Real := (alpha - 1) / alpha
  have ht_nonneg : 0 <= t := by
    dsimp [t]
    exact div_nonneg (sub_nonneg.mpr halpha.le) halpha_pos.le
  have ht_le_one : t <= 1 := by
    dsimp [t]
    exact (div_le_one halpha_pos).2 (by linarith)
  have hexp : -t = (1 - alpha) / alpha := by
    dsimp [t]
    field_simp [halpha_pos.ne']
    ring
  have hpow : CFC.rpow tau ((1 - alpha) / alpha) <=
      CFC.rpow sigma ((1 - alpha) / alpha) := by
    rw [← hexp]
    exact cMatrix_rpow_neg_le_rpow_neg_of_posDef_le hsigma htau
      ht_nonneg ht_le_one hsigma_tau
  have houter : sandwichedRenyiReferenceOuter rho tau alpha <=
      sandwichedRenyiReferenceOuter rho sigma alpha :=
    sandwichedRenyiReferenceOuter_le_of_rpow_le rho hpow
  have hnormOuter :
      psdSchattenPNorm (sandwichedRenyiReferenceOuter rho tau alpha)
          (sandwichedRenyiReferenceOuter_posSemidef rho htau.posSemidef alpha)
          ⟨alpha, halpha_pos⟩ <=
        psdSchattenPNorm (sandwichedRenyiReferenceOuter rho sigma alpha)
          (sandwichedRenyiReferenceOuter_posSemidef rho hsigma.posSemidef alpha)
          ⟨alpha, halpha_pos⟩ :=
    psdSchattenPNorm_mono_of_le
      (sandwichedRenyiReferenceOuter_posSemidef rho htau.posSemidef alpha)
      (sandwichedRenyiReferenceOuter_posSemidef rho hsigma.posSemidef alpha)
      halpha houter
  have hnorm :
      psdSchattenPNorm (sandwichedRenyiReferenceInner rho tau alpha)
          (sandwichedRenyiReferenceInner_posSemidef rho htau.posSemidef alpha)
          ⟨alpha, halpha_pos⟩ <=
        psdSchattenPNorm (sandwichedRenyiReferenceInner rho sigma alpha)
          (sandwichedRenyiReferenceInner_posSemidef rho hsigma.posSemidef alpha)
          ⟨alpha, halpha_pos⟩ := by
    rw [sandwichedRenyiReferenceInner_psdSchattenPNorm_eq_outer rho
        htau.posSemidef halpha_pos halpha_ne_one,
      sandwichedRenyiReferenceInner_psdSchattenPNorm_eq_outer rho
        hsigma.posSemidef halpha_pos halpha_ne_one]
    exact hnormOuter
  have hnormTauPos :
      0 < psdSchattenPNorm (sandwichedRenyiReferenceInner rho tau alpha)
        (sandwichedRenyiReferenceInner_posSemidef rho htau.posSemidef alpha)
        ⟨alpha, halpha_pos⟩ :=
    psdSchattenPNorm_pos_of_ne_zero _ _
      (sandwichedRenyiReferenceInner_ne_zero_of_reference_posDef rho htau alpha)
  have hlog :
      log2 (psdSchattenPNorm (sandwichedRenyiReferenceInner rho tau alpha)
          (sandwichedRenyiReferenceInner_posSemidef rho htau.posSemidef alpha)
          ⟨alpha, halpha_pos⟩) <=
        log2 (psdSchattenPNorm (sandwichedRenyiReferenceInner rho sigma alpha)
          (sandwichedRenyiReferenceInner_posSemidef rho hsigma.posSemidef alpha)
          ⟨alpha, halpha_pos⟩) := by
    unfold log2
    exact div_le_div_of_nonneg_right (Real.log_le_log hnormTauPos hnorm)
      (le_of_lt <| Real.log_pos one_lt_two)
  have hSupportTau : Matrix.Supports rho.matrix tau :=
    Matrix.Supports.of_right_posDef rho.matrix tau htau
  have hSupportSigma : Matrix.Supports rho.matrix sigma :=
    Matrix.Supports.of_right_posDef rho.matrix sigma hsigma
  rw [sandwichedRenyiPSDReferenceHighAlphaFinite_eq_schatten_log_of_supports
      rho htau.posSemidef hSupportTau halpha,
    sandwichedRenyiPSDReferenceHighAlphaFinite_eq_schatten_log_of_supports
      rho hsigma.posSemidef hSupportSigma halpha]
  exact mul_le_mul_of_nonneg_left hlog
    (le_of_lt <| div_pos halpha_pos <| sub_pos.mpr halpha)

/-- Supported singular high-order finite branches inherit reference
antitonicity from positive regularization. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_antitone_reference
    (rho : State a) {sigma tau : CMatrix a}
    (hsigma : sigma.PosSemidef) (htau : tau.PosSemidef)
    (hsigma_tau : sigma <= tau)
    (hSupportSigma : Matrix.Supports rho.matrix sigma)
    {alpha : Real} (halpha : 1 < alpha) :
    sandwichedRenyiPSDReferenceHighAlphaFinite rho tau htau alpha <=
      sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma alpha := by
  have hSupportTau := supports_of_supports_of_reference_le rho hsigma
    hsigma_tau hSupportSigma
  have htauLimit :=
    sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve_tendsto_of_supports
      rho htau hSupportTau alpha halpha
  have hsigmaLimit :=
    sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve_tendsto_of_supports
      rho hsigma hSupportSigma alpha halpha
  apply le_of_tendsto_of_tendsto htauLimit hsigmaLimit
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  have hepsilon_pos : 0 < epsilon := hepsilon
  unfold sandwichedRenyiPSDReferenceHighAlphaFiniteRegularizedInputCurve
  rw [dif_pos hepsilon_pos, dif_pos hepsilon_pos]
  apply sandwichedRenyiPSDReferenceHighAlphaFinite_antitone_reference_of_posDef
  · exact sandwichedRenyiReferenceRegularization_posDef hsigma hepsilon_pos
  · exact sandwichedRenyiReferenceRegularization_posDef htau hepsilon_pos
  · unfold sandwichedRenyiReferenceRegularization
    exact add_le_add_left hsigma_tau _
  · exact halpha

/-- Extended-real high-order sandwiched Renyi divergence is antitone in every
PSD reference, including the unsupported `+infinity` branch. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_antitone_reference
    (rho : State a) {sigma tau : CMatrix a}
    (hsigma : sigma.PosSemidef) (htau : tau.PosSemidef)
    (hsigma_tau : sigma <= tau) {alpha : Real} (halpha : 1 < alpha) :
    sandwichedRenyiPSDReferenceHighAlphaE rho tau htau alpha <=
      sandwichedRenyiPSDReferenceHighAlphaE rho sigma hsigma alpha := by
  by_cases hSupportSigma : Matrix.Supports rho.matrix sigma
  · have hSupportTau := supports_of_supports_of_reference_le rho hsigma
      hsigma_tau hSupportSigma
    rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
        rho htau alpha hSupportTau,
      sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
        rho hsigma alpha hSupportSigma]
    exact EReal.coe_le_coe_iff.mpr
      (sandwichedRenyiPSDReferenceHighAlphaFinite_antitone_reference rho
        hsigma htau hsigma_tau hSupportSigma halpha)
  · rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_top_of_not_supports
      rho hsigma alpha hSupportSigma]
    exact le_top

/-- The Umegaki trace-log endpoint is antitone in its PSD reference.  The
proof is the closed-order limit of the already proved high-order property as
`alpha -> 1+`. -/
theorem relativeEntropyPSDReferenceTraceLogE_antitone_reference
    (rho : State a) {sigma tau : CMatrix a}
    (hsigma : sigma.PosSemidef) (htau : tau.PosSemidef)
    (hsigma_tau : sigma <= tau) :
    relativeEntropyPSDReferenceTraceLogE rho tau htau <=
      relativeEntropyPSDReferenceTraceLogE rho sigma hsigma := by
  by_cases hSupportSigma : Matrix.Supports rho.matrix sigma
  · have hSupportTau := supports_of_supports_of_reference_le rho hsigma
      hsigma_tau hSupportSigma
    rw [relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports
        rho htau hSupportTau,
      relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports
        rho hsigma hSupportSigma]
    letI : Filter.NeBot relativeEntropyHighAlphaRightToOne :=
      relativeEntropyHighAlphaRightToOne_neBot
    apply le_of_tendsto_of_tendsto
      (sandwichedRenyiPSDReferenceHighAlphaCurve_tendsto_traceLogFinite_of_supports
        rho htau hSupportTau)
      (sandwichedRenyiPSDReferenceHighAlphaCurve_tendsto_traceLogFinite_of_supports
        rho hsigma hSupportSigma)
    exact Filter.Eventually.of_forall fun alpha => by
      unfold sandwichedRenyiPSDReferenceHighAlphaCurve
      rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt
          rho htau alpha.2,
        sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt
          rho hsigma alpha.2]
      exact sandwichedRenyiPSDReferenceHighAlphaE_antitone_reference rho
        hsigma htau hsigma_tau alpha.2
  · rw [relativeEntropyPSDReferenceTraceLogE_eq_top_of_not_supports
      rho hsigma hSupportSigma]
    exact le_top

/-- Source-facing reference dominance for the canonical extended-real
sandwiched Renyi divergence on the full data-processing range
`1/2 <= alpha < infinity`, including `alpha = 1`. -/
theorem sandwichedRenyiPSDReferenceE_antitone_reference
    (rho : State a) {sigma tau : CMatrix a}
    (hsigma : sigma.PosSemidef) (htau : tau.PosSemidef)
    (hsigma_tau : sigma <= tau) {alpha : Real}
    (halpha_half : 1 / 2 <= alpha) :
    sandwichedRenyiPSDReferenceE rho tau htau alpha <=
      sandwichedRenyiPSDReferenceE rho sigma hsigma alpha := by
  by_cases halpha_lt_one : alpha < 1
  · rw [sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one
        rho htau halpha_lt_one,
      sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one
        rho hsigma halpha_lt_one]
    exact sandwichedRenyiPSDReferenceLowAlphaE_antitone_reference rho
      hsigma htau hsigma_tau halpha_half halpha_lt_one
  · by_cases halpha_eq_one : alpha = 1
    · rw [sandwichedRenyiPSDReferenceE_eq_traceLogE_of_eq_one
          rho htau halpha_eq_one,
        sandwichedRenyiPSDReferenceE_eq_traceLogE_of_eq_one
          rho hsigma halpha_eq_one]
      exact relativeEntropyPSDReferenceTraceLogE_antitone_reference rho
        hsigma htau hsigma_tau
    · have halpha_one_lt : 1 < alpha :=
        lt_of_le_of_ne (le_of_not_gt halpha_lt_one) (Ne.symm halpha_eq_one)
      rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt
          rho htau halpha_one_lt,
        sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt
          rho hsigma halpha_one_lt]
      exact sandwichedRenyiPSDReferenceHighAlphaE_antitone_reference rho
        hsigma htau hsigma_tau halpha_one_lt

/-- Compatibility theorem for the legacy finite positive-definite reference
API.  Its hypotheses expose the same source range as the canonical theorem. -/
theorem sandwichedRenyiReference_antitone_reference
    (rho : State a) {sigma tau : CMatrix a}
    (hrho : rho.matrix.PosDef) (hsigma : sigma.PosDef) (htau : tau.PosDef)
    (hsigma_tau : sigma <= tau) {alpha : Real}
    (halpha_half : 1 / 2 <= alpha) (halpha_ne_one : alpha ≠ 1) :
    sandwichedRenyiReference rho tau hrho htau alpha
        (lt_of_lt_of_le (by norm_num) halpha_half) halpha_ne_one <=
      sandwichedRenyiReference rho sigma hrho hsigma alpha
        (lt_of_lt_of_le (by norm_num) halpha_half) halpha_ne_one := by
  have halpha_pos : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha_half
  have hcanonical := sandwichedRenyiPSDReferenceE_antitone_reference rho
    hsigma.posSemidef htau.posSemidef hsigma_tau halpha_half
  rcases lt_or_gt_of_ne halpha_ne_one with halpha_lt_one | halpha_one_lt
  · rw [sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one
        rho htau.posSemidef halpha_lt_one,
      sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one
        rho hsigma.posSemidef halpha_lt_one,
      sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_reference_posDef
        rho hrho htau alpha halpha_pos halpha_ne_one,
      sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_reference_posDef
        rho hrho hsigma alpha halpha_pos halpha_ne_one] at hcanonical
    exact EReal.coe_le_coe_iff.mp hcanonical
  · rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt
        rho htau.posSemidef halpha_one_lt,
      sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt
        rho hsigma.posSemidef halpha_one_lt,
      sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_reference_posDef
        rho hrho htau alpha halpha_pos halpha_ne_one,
      sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_reference_posDef
        rho hrho hsigma alpha halpha_pos halpha_ne_one] at hcanonical
    exact EReal.coe_le_coe_iff.mp hcanonical

end State

end

end QIT
