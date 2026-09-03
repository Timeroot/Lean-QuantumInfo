/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.FrankLieb.DPI
public import QIT.HypothesisTesting.MutualInformation
public import QIT.Information.Entropy.Log2Lemmas

/-!
# Hypothesis testing to sandwiched-Renyi comparison

This module starts the source route for
[KhatriWilde2024Principles, Chapters/entropies.tex:7004-7029].  The source
statement allows the second hypothesis to be a positive semidefinite operator,
so the local API below mirrors the existing beta-first hypothesis-testing
relative entropy definitions with a PSD matrix reference.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

namespace HypothesisTestingEffect

variable {rho : State a} {epsilon : ℝ}

/-- Type-II error of a feasible effect against a PSD matrix reference. -/
def typeIIErrorPSD (Lambda : HypothesisTestingEffect rho epsilon) (sigma : CMatrix a) : ℝ :=
  ((sigma * Lambda.effect).trace).re

theorem typeIIErrorPSD_eq_state (Lambda : HypothesisTestingEffect rho epsilon)
    (sigma : State a) :
    Lambda.typeIIErrorPSD sigma.matrix = Lambda.typeIIError sigma := by
  rfl

theorem typeIIErrorPSD_nonneg (Lambda : HypothesisTestingEffect rho epsilon)
    {sigma : CMatrix a} (hsigma : sigma.PosSemidef) :
    0 ≤ Lambda.typeIIErrorPSD sigma := by
  unfold typeIIErrorPSD
  exact cMatrix_trace_mul_posSemidef_re_nonneg hsigma Lambda.pos

/-- Under support domination, a feasible effect with `epsilon < 1` has
strictly positive PSD type-II error.  This is the support-domain handoff in the
source proof of `prop:sandwich-to-htre`. -/
theorem typeIIErrorPSD_pos_of_supports (Lambda : HypothesisTestingEffect rho epsilon)
    {sigma : CMatrix a} (hsigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma) (hε_lt_one : epsilon < 1) :
    0 < Lambda.typeIIErrorPSD sigma := by
  classical
  let Phi : Channel a Bool := Channel.measure Lambda.toBinaryHypothesisTest
  let e : Bool → ℂ := fun b => if b then 1 else 0
  have hOutSupport : Matrix.Supports (Phi.map rho.matrix) (Phi.map sigma) :=
    State.channel_map_supports Phi hsigma hSupport
  have hq_nonneg : 0 ≤ Lambda.typeIIErrorPSD sigma :=
    Lambda.typeIIErrorPSD_nonneg hsigma
  by_contra hq_not_pos
  have hq_zero : Lambda.typeIIErrorPSD sigma = 0 :=
    le_antisymm (not_lt.mp hq_not_pos) hq_nonneg
  have htrace_q_zero : (sigma * Lambda.effect).trace = 0 := by
    apply Complex.ext
    · simpa [typeIIErrorPSD] using hq_zero
    · simpa using trace_mul_posSemidef_im_eq_zero hsigma Lambda.pos
  have hPhiSigma_e : (Phi.map sigma).mulVec e = 0 := by
    ext b
    cases b <;>
      simp [Phi, e, Channel.measure_map, Matrix.mulVec, dotProduct,
        HypothesisTestingEffect.toBinaryHypothesisTest, htrace_q_zero]
  have hPhiRho_e : (Phi.map rho.matrix).mulVec e = 0 :=
    hOutSupport e hPhiSigma_e
  have haccept_zero_complex : (rho.matrix * Lambda.effect).trace = 0 := by
    have htrue := congrFun hPhiRho_e true
    simpa [Phi, e, Channel.measure_map, Matrix.mulVec, dotProduct,
      HypothesisTestingEffect.toBinaryHypothesisTest] using htrue
  have haccept_zero : effectAcceptProbability rho Lambda.effect = 0 := by
    unfold effectAcceptProbability
    exact congrArg Complex.re haccept_zero_complex
  have haccept_pos : 0 < effectAcceptProbability rho Lambda.effect :=
    (sub_pos.mpr hε_lt_one).trans_le Lambda.accept_ge
  linarith

end HypothesisTestingEffect

namespace State

variable (rho : State a) (sigma : CMatrix a) (epsilon : ℝ)

/-- Candidate set for the PSD-reference beta quantity. -/
def hypothesisTestingBetaPSDCandidateSet : Set ℝ :=
  {beta | ∃ Lambda : HypothesisTestingEffect rho epsilon,
    beta = Lambda.typeIIErrorPSD sigma}

/-- Hypothesis-testing beta with a PSD matrix reference. -/
def hypothesisTestingBetaPSD : ℝ :=
  sInf (rho.hypothesisTestingBetaPSDCandidateSet sigma epsilon)

/-- PSD-reference hypothesis-testing relative entropy in bits. -/
def hypothesisTestingRelativeEntropyPSD : ℝ :=
  -log2 (rho.hypothesisTestingBetaPSD sigma epsilon)

/-- PSD-reference extended-real hypothesis-testing relative entropy. -/
def hypothesisTestingRelativeEntropyPSDE : EReal :=
  if rho.hypothesisTestingBetaPSD sigma epsilon = 0 then ⊤
  else (rho.hypothesisTestingRelativeEntropyPSD sigma epsilon : EReal)

theorem hypothesisTestingBetaPSD_eq_sInf :
    rho.hypothesisTestingBetaPSD sigma epsilon =
      sInf (rho.hypothesisTestingBetaPSDCandidateSet sigma epsilon) :=
  rfl

theorem hypothesisTestingRelativeEntropyPSD_eq :
    rho.hypothesisTestingRelativeEntropyPSD sigma epsilon =
      -log2 (rho.hypothesisTestingBetaPSD sigma epsilon) :=
  rfl

theorem hypothesisTestingRelativeEntropyPSDE_eq :
    rho.hypothesisTestingRelativeEntropyPSDE sigma epsilon =
      if rho.hypothesisTestingBetaPSD sigma epsilon = 0 then ⊤
      else (rho.hypothesisTestingRelativeEntropyPSD sigma epsilon : EReal) :=
  rfl

theorem hypothesisTestingBetaPSDCandidateSet_nonempty_of_nonneg (hε : 0 ≤ epsilon) :
    (rho.hypothesisTestingBetaPSDCandidateSet sigma epsilon).Nonempty := by
  refine ⟨(HypothesisTestingEffect.identity rho epsilon hε).typeIIErrorPSD sigma, ?_⟩
  refine ⟨HypothesisTestingEffect.identity rho epsilon hε, ?_⟩
  rfl

theorem hypothesisTestingBetaPSD_nonneg
    (hsigma : sigma.PosSemidef) (hε : 0 ≤ epsilon) :
    0 ≤ rho.hypothesisTestingBetaPSD sigma epsilon := by
  rw [hypothesisTestingBetaPSD_eq_sInf]
  exact le_csInf
    (rho.hypothesisTestingBetaPSDCandidateSet_nonempty_of_nonneg sigma epsilon hε)
    (by
      intro beta hbeta
      rcases hbeta with ⟨Lambda, rfl⟩
      exact Lambda.typeIIErrorPSD_nonneg hsigma)

theorem hypothesisTestingBetaPSD_le_of_effect
    (hsigma : sigma.PosSemidef)
    (Lambda : HypothesisTestingEffect rho epsilon) :
    rho.hypothesisTestingBetaPSD sigma epsilon ≤ Lambda.typeIIErrorPSD sigma := by
  rw [hypothesisTestingBetaPSD_eq_sInf]
  refine csInf_le ?_ ⟨Lambda, rfl⟩
  refine ⟨0, ?_⟩
  intro beta hbeta
  rcases hbeta with ⟨Lambda, rfl⟩
  exact Lambda.typeIIErrorPSD_nonneg hsigma

theorem hypothesisTestingRelativeEntropyPSDE_eq_state (sigma : State a) :
    rho.hypothesisTestingRelativeEntropyPSDE sigma.matrix epsilon =
      rho.hypothesisTestingRelativeEntropy sigma epsilon := by
  simp [hypothesisTestingRelativeEntropyPSDE, hypothesisTestingRelativeEntropy,
    hypothesisTestingRelativeEntropyPSD, hypothesisTestingRelativeEntropyFinite,
    hypothesisTestingBetaPSD, hypothesisTestingBeta,
    hypothesisTestingBetaPSDCandidateSet, hypothesisTestingBetaCandidateSet,
    HypothesisTestingEffect.typeIIErrorPSD_eq_state]

private theorem sandwich_log2_rpow_pos {x : ℝ} (hx : 0 < x) (y : ℝ) :
    log2 (x ^ y) = y * log2 x := by
  unfold log2
  rw [Real.log_rpow hx y]
  ring

private theorem rpow_two_neg_le_of_neg_log2_le {q C : ℝ} (hq : 0 < q)
    (h : -log2 q ≤ C) :
    Real.rpow 2 (-C) ≤ q := by
  have hexp : -C ≤ log2 q := by linarith
  have hpow :=
    Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ))
      (by norm_num : (1 : ℝ) ≤ 2) hexp
  rw [← rpow_two_log2_pos hq]
  exact hpow

private theorem scalar_binary_sandwiched_lower
    {p q T epsilon alpha : ℝ} (halpha : 1 < alpha) (hepsilon : epsilon < 1)
    (hp : 1 - epsilon ≤ p) (hq : 0 < q)
    (hT : p ^ alpha * q ^ (1 - alpha) ≤ T) :
    alpha / (alpha - 1) * log2 (1 - epsilon) - log2 q ≤
      (1 / (alpha - 1)) * log2 T := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hcoef_pos : 0 < alpha - 1 := sub_pos.mpr halpha
  have heps_pos : 0 < 1 - epsilon := sub_pos.mpr hepsilon
  have hp_pow : (1 - epsilon) ^ alpha ≤ p ^ alpha :=
    Real.rpow_le_rpow (le_of_lt heps_pos) hp (le_of_lt halpha_pos)
  have hqpow_nonneg : 0 ≤ q ^ (1 - alpha) := Real.rpow_nonneg (le_of_lt hq) _
  have hx_le :
      (1 - epsilon) ^ alpha * q ^ (1 - alpha) ≤
        p ^ alpha * q ^ (1 - alpha) :=
    mul_le_mul_of_nonneg_right hp_pow hqpow_nonneg
  have hxT : (1 - epsilon) ^ alpha * q ^ (1 - alpha) ≤ T := hx_le.trans hT
  have hx_pos : 0 < (1 - epsilon) ^ alpha * q ^ (1 - alpha) :=
    mul_pos (Real.rpow_pos_of_pos heps_pos alpha)
      (Real.rpow_pos_of_pos hq (1 - alpha))
  have hlog := log2_mono_of_pos hx_pos hxT
  have hlogx :
      log2 ((1 - epsilon) ^ alpha * q ^ (1 - alpha)) =
        alpha * log2 (1 - epsilon) + (1 - alpha) * log2 q := by
    rw [log2_mul (ne_of_gt (Real.rpow_pos_of_pos heps_pos alpha))
      (ne_of_gt (Real.rpow_pos_of_pos hq (1 - alpha)))]
    rw [sandwich_log2_rpow_pos heps_pos alpha,
      sandwich_log2_rpow_pos hq (1 - alpha)]
  rw [hlogx] at hlog
  calc
    alpha / (alpha - 1) * log2 (1 - epsilon) - log2 q =
        (1 / (alpha - 1)) *
          (alpha * log2 (1 - epsilon) + (1 - alpha) * log2 q) := by
          field_simp [ne_of_gt hcoef_pos]
          ring
    _ ≤ (1 / (alpha - 1)) * log2 T := by
          exact mul_le_mul_of_nonneg_left hlog
            (one_div_nonneg.mpr (le_of_lt hcoef_pos))

private theorem measurement_map_eq_diagonal_re (M : POVM Bool a)
    {X : CMatrix a} (hX : X.PosSemidef) :
    (Channel.measure M).map X =
      (Matrix.diagonal fun b : Bool => (((X * M.effects b).trace).re : ℂ)) := by
  ext i j
  cases i <;> cases j
  all_goals simp [Channel.measure_map, Matrix.diagonal]
  all_goals
    apply Complex.ext <;>
      simp [trace_mul_posSemidef_im_eq_zero hX (M.pos false),
        trace_mul_posSemidef_im_eq_zero hX (M.pos true)]

private theorem measurement_map_rpow_eq_diagonal_re (M : POVM Bool a)
    {X : CMatrix a} (hX : X.PosSemidef) (s : ℝ) :
    CFC.rpow ((Channel.measure M).map X) s =
      (Matrix.diagonal fun b : Bool =>
        ((((X * M.effects b).trace).re ^ s : ℝ) : ℂ)) := by
  let d : Bool → ℝ := fun b => ((X * M.effects b).trace).re
  have hd : ∀ b, 0 ≤ d b := by
    intro b
    exact cMatrix_trace_mul_posSemidef_re_nonneg hX (M.pos b)
  have hdiag :
      (Channel.measure M).map X =
        (Matrix.diagonal fun b : Bool => ((d b : ℝ) : ℂ)) := by
    simpa [d] using measurement_map_eq_diagonal_re M hX
  rw [hdiag]
  have hpow := cMatrix_rpow_diagonal_ofReal (a := Bool) d hd s
  simpa [d] using hpow

private theorem measurement_sandwiched_inner_true_true_re
    {rho : State a} {epsilon : ℝ} (Lambda : HypothesisTestingEffect rho epsilon)
    {sigma : CMatrix a} (hsigma : sigma.PosSemidef) {alpha : ℝ}
    (hqpos : 0 < Lambda.typeIIErrorPSD sigma) :
    let Phi : Channel a Bool := Channel.measure Lambda.toBinaryHypothesisTest
    ((sandwichedRenyiReferenceInner (Phi.applyState rho) (Phi.map sigma) alpha)
        true true).re =
      effectAcceptProbability rho Lambda.effect *
        (Lambda.typeIIErrorPSD sigma) ^ ((1 - alpha) / alpha) := by
  intro Phi
  let s : ℝ := (1 - alpha) / (2 * alpha)
  have hrefpow_diag :
      CFC.rpow (Phi.map sigma) s =
        (Matrix.diagonal fun b : Bool =>
          ((((sigma * Lambda.toBinaryHypothesisTest.effects b).trace).re ^ s : ℝ) :
            ℂ)) := by
    simpa [Phi] using
      measurement_map_rpow_eq_diagonal_re Lambda.toBinaryHypothesisTest hsigma s
  have hrho_true :
      ((Phi.applyState rho).matrix true true) =
        (effectAcceptProbability rho Lambda.effect : ℂ) := by
    exact Complex.ext
      (by
        simp [Phi, Channel.applyState, Channel.measure_map, effectAcceptProbability,
          HypothesisTestingEffect.toBinaryHypothesisTest])
      (by
        simp [Phi, Channel.applyState, Channel.measure_map,
          HypothesisTestingEffect.toBinaryHypothesisTest,
          trace_mul_posSemidef_im_eq_zero rho.pos Lambda.pos])
  have hq_entry :
      ((sigma * Lambda.toBinaryHypothesisTest.effects true).trace).re =
        Lambda.typeIIErrorPSD sigma := by
    rfl
  have hpowprod :
      (Lambda.typeIIErrorPSD sigma) ^ s *
        (Lambda.typeIIErrorPSD sigma) ^ s =
      (Lambda.typeIIErrorPSD sigma) ^ ((1 - alpha) / alpha) := by
    rw [← Real.rpow_add hqpos]
    congr 1
    dsimp [s]
    field_simp
    ring
  unfold sandwichedRenyiReferenceInner
  change ((CFC.rpow (Phi.map sigma) s * (Phi.applyState rho).matrix *
      CFC.rpow (Phi.map sigma) s) true true).re =
    effectAcceptProbability rho Lambda.effect *
      Lambda.typeIIErrorPSD sigma ^ ((1 - alpha) / alpha)
  rw [hrefpow_diag]
  simp [Matrix.mul_apply, hrho_true, hq_entry, hpowprod, mul_assoc, mul_comm,
    mul_left_comm]

private theorem measurement_sandwiched_tracePower_accept_lower
    {rho : State a} {epsilon : ℝ} (Lambda : HypothesisTestingEffect rho epsilon)
    {sigma : CMatrix a} (hsigma : sigma.PosSemidef) {alpha : ℝ}
    (halpha : 1 < alpha) (hqpos : 0 < Lambda.typeIIErrorPSD sigma) :
    let Phi : Channel a Bool := Channel.measure Lambda.toBinaryHypothesisTest
    effectAcceptProbability rho Lambda.effect ^ alpha *
        Lambda.typeIIErrorPSD sigma ^ (1 - alpha) ≤
      psdTracePower (sandwichedRenyiReferenceInner (Phi.applyState rho)
          (Phi.map sigma) alpha)
        (sandwichedRenyiReferenceInner_posSemidef (Phi.applyState rho)
          (Phi.mapsPositive sigma hsigma) alpha) alpha := by
  intro Phi
  let B : CMatrix Bool :=
    sandwichedRenyiReferenceInner (Phi.applyState rho) (Phi.map sigma) alpha
  let hB : B.PosSemidef :=
    sandwichedRenyiReferenceInner_posSemidef (Phi.applyState rho)
      (Phi.mapsPositive sigma hsigma) alpha
  have hdiag :=
    measurement_sandwiched_inner_true_true_re Lambda hsigma hqpos (alpha := alpha)
  have hp_nonneg : 0 ≤ effectAcceptProbability rho Lambda.effect := by
    unfold effectAcceptProbability
    exact cMatrix_trace_mul_posSemidef_re_nonneg rho.pos Lambda.pos
  have hq_nonneg : 0 ≤ Lambda.typeIIErrorPSD sigma := le_of_lt hqpos
  have hterm_eq :
      (B true true).re ^ alpha =
        effectAcceptProbability rho Lambda.effect ^ alpha *
          Lambda.typeIIErrorPSD sigma ^ (1 - alpha) := by
    have hpowmul :
        (effectAcceptProbability rho Lambda.effect *
            Lambda.typeIIErrorPSD sigma ^ ((1 - alpha) / alpha)) ^ alpha =
          effectAcceptProbability rho Lambda.effect ^ alpha *
            (Lambda.typeIIErrorPSD sigma ^ ((1 - alpha) / alpha)) ^ alpha := by
      rw [Real.mul_rpow hp_nonneg (Real.rpow_nonneg hq_nonneg _)]
    have hqpow :
        (Lambda.typeIIErrorPSD sigma ^ ((1 - alpha) / alpha)) ^ alpha =
          Lambda.typeIIErrorPSD sigma ^ (1 - alpha) := by
      rw [← Real.rpow_mul hq_nonneg]
      field_simp [ne_of_gt (lt_trans zero_lt_one halpha)]
    rw [show (B true true).re =
        effectAcceptProbability rho Lambda.effect *
          Lambda.typeIIErrorPSD sigma ^ ((1 - alpha) / alpha) from by
      simpa [Phi, B] using hdiag]
    rw [hpowmul, hqpow]
  have hterm_le_sum :
      (B true true).re ^ alpha ≤
        (Finset.univ.sum fun i : Bool => (B i i).re ^ alpha) := by
    exact Finset.single_le_sum
      (by
        intro i _hi
        exact Real.rpow_nonneg (posSemidef_diagonal_re_nonneg hB i) alpha)
      (Finset.mem_univ true)
  have hsum_le :=
    posSemidef_sum_diagonal_re_rpow_le_psdTracePower hB (le_of_lt halpha)
  calc
    effectAcceptProbability rho Lambda.effect ^ alpha *
        Lambda.typeIIErrorPSD sigma ^ (1 - alpha)
        = (B true true).re ^ alpha := hterm_eq.symm
    _ ≤ Finset.univ.sum fun i : Bool => (B i i).re ^ alpha := hterm_le_sum
    _ ≤ psdTracePower B hB alpha := hsum_le

/-- If all feasible PSD type-II errors have the same positive exponential
lower bound, then the PSD-reference hypothesis-testing relative entropy is
bounded by the corresponding real constant. -/
theorem hypothesisTestingRelativeEntropyPSDE_le_of_effect_rpow_lower_bound
    (rho : State a) {sigma : CMatrix a}
    {epsilon C : ℝ} (hε : 0 ≤ epsilon)
    (hlower : ∀ Lambda : HypothesisTestingEffect rho epsilon,
      Real.rpow 2 (-C) ≤ Lambda.typeIIErrorPSD sigma) :
    rho.hypothesisTestingRelativeEntropyPSDE sigma epsilon ≤ (C : EReal) := by
  let t : ℝ := Real.rpow 2 (-C)
  have ht_pos : 0 < t := Real.rpow_pos_of_pos (by norm_num) (-C)
  have hbeta_ge : t ≤ rho.hypothesisTestingBetaPSD sigma epsilon := by
    rw [hypothesisTestingBetaPSD_eq_sInf]
    exact le_csInf
      (rho.hypothesisTestingBetaPSDCandidateSet_nonempty_of_nonneg sigma epsilon hε)
      (by
        intro beta hbeta
        rcases hbeta with ⟨Lambda, rfl⟩
        exact hlower Lambda)
  have hbeta_pos : 0 < rho.hypothesisTestingBetaPSD sigma epsilon :=
    ht_pos.trans_le hbeta_ge
  have hlog :
      log2 t ≤ log2 (rho.hypothesisTestingBetaPSD sigma epsilon) := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log ht_pos hbeta_ge) (le_of_lt (Real.log_pos one_lt_two))
  rw [hypothesisTestingRelativeEntropyPSDE_eq, if_neg hbeta_pos.ne']
  change ((rho.hypothesisTestingRelativeEntropyPSD sigma epsilon : ℝ) : EReal) ≤ (C : EReal)
  norm_num
  rw [hypothesisTestingRelativeEntropyPSD_eq]
  exact_mod_cast (by
    calc
      -log2 (rho.hypothesisTestingBetaPSD sigma epsilon) ≤ -log2 t := neg_le_neg hlog
      _ = C := by simpa [t] using neg_log2_rpow_two_neg C)

/-- Unsupported high-`alpha` branch of the source comparison.  When the state is
not supported by the PSD reference, the sandwiched-Renyi side is `+∞`. -/
theorem hypothesisTestingRelativeEntropyPSDE_le_sandwichedRenyiPSDReferenceE_add_of_not_supports
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosSemidef)
    {epsilon alpha : ℝ} (halpha : 1 < alpha)
    (hSupport : ¬ Matrix.Supports rho.matrix sigma) :
    rho.hypothesisTestingRelativeEntropyPSDE sigma epsilon ≤
      sandwichedRenyiPSDReferenceE rho sigma hsigma alpha +
        ((alpha / (alpha - 1) * log2 (1 / (1 - epsilon)) : ℝ) : EReal) := by
  rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt rho hsigma halpha]
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_top_of_not_supports
    rho hsigma alpha hSupport]
  rw [EReal.top_add_coe]
  exact le_top

private theorem typeIIErrorPSD_rpow_lower_bound_of_sandwichedRenyi
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosSemidef)
    {epsilon alpha : ℝ} (hε_lt_one : epsilon < 1) (halpha : 1 < alpha)
    (hSupport : Matrix.Supports rho.matrix sigma)
    (Lambda : HypothesisTestingEffect rho epsilon) :
    Real.rpow 2
        (-(rho.sandwichedRenyiPSDReferenceHighAlphaFinite sigma hsigma alpha +
          alpha / (alpha - 1) * log2 (1 / (1 - epsilon)))) ≤
      Lambda.typeIIErrorPSD sigma := by
  let Phi : Channel a Bool := Channel.measure Lambda.toBinaryHypothesisTest
  let q : ℝ := Lambda.typeIIErrorPSD sigma
  have hqpos : 0 < q := by
    simpa [q] using
      Lambda.typeIIErrorPSD_pos_of_supports hsigma hSupport hε_lt_one
  let T : ℝ :=
    psdTracePower (sandwichedRenyiReferenceInner (Phi.applyState rho)
        (Phi.map sigma) alpha)
      (sandwichedRenyiReferenceInner_posSemidef (Phi.applyState rho)
        (Phi.mapsPositive sigma hsigma) alpha) alpha
  have htrace :
      effectAcceptProbability rho Lambda.effect ^ alpha * q ^ (1 - alpha) ≤ T := by
    simpa [Phi, q, T] using
      measurement_sandwiched_tracePower_accept_lower Lambda hsigma halpha hqpos
  have hmeasureLower :
      alpha / (alpha - 1) * log2 (1 - epsilon) - log2 q ≤
        (Phi.applyState rho).sandwichedRenyiPSDReferenceHighAlphaFinite
          (Phi.map sigma) (Phi.mapsPositive sigma hsigma) alpha := by
    simpa [T, sandwichedRenyiPSDReferenceHighAlphaFinite] using
      scalar_binary_sandwiched_lower halpha hε_lt_one Lambda.accept_ge hqpos htrace
  have hOutSupport :
      Matrix.Supports (Phi.applyState rho).matrix (Phi.map sigma) :=
    channel_applyState_supports_of_supports rho hsigma Phi hSupport
  have hDPIE :=
    sandwichedRenyiPSDReferenceE_dataProcessing_channel_ge_of_half_le_lt_one_or_one_lt
      rho hsigma Phi alpha (Or.inr halpha)
  rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt rho hsigma halpha,
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      rho hsigma alpha hSupport,
    sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt
      (Phi.applyState rho) (Phi.mapsPositive sigma hsigma) halpha,
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      (Phi.applyState rho) (Phi.mapsPositive sigma hsigma) alpha hOutSupport] at hDPIE
  have hDPI :
      (Phi.applyState rho).sandwichedRenyiPSDReferenceHighAlphaFinite
          (Phi.map sigma) (Phi.mapsPositive sigma hsigma) alpha ≤
        rho.sandwichedRenyiPSDReferenceHighAlphaFinite sigma hsigma alpha := by
    exact_mod_cast hDPIE
  have hsource :
      alpha / (alpha - 1) * log2 (1 - epsilon) - log2 q ≤
        rho.sandwichedRenyiPSDReferenceHighAlphaFinite sigma hsigma alpha :=
    hmeasureLower.trans hDPI
  have hinv : log2 (1 / (1 - epsilon)) = -log2 (1 - epsilon) :=
    log2_one_div (1 - epsilon)
  have hneg :
      -log2 q ≤
        rho.sandwichedRenyiPSDReferenceHighAlphaFinite sigma hsigma alpha +
          alpha / (alpha - 1) * log2 (1 / (1 - epsilon)) := by
    rw [hinv]
    linarith
  simpa [q] using rpow_two_neg_le_of_neg_log2_le hqpos hneg

/-- Khatri--Wilde hypothesis-testing to sandwiched-Renyi comparison, with a
PSD matrix reference and the extended-real support convention.

This is the state-level source theorem `prop:sandwich-to-htre` from
[KhatriWilde2024Principles, Chapters/entropies.tex:7004-7029]. -/
theorem hypothesisTestingRelativeEntropyPSDE_le_sandwichedRenyiPSDReferenceE_add
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosSemidef)
    {epsilon alpha : ℝ} (hε_nonneg : 0 ≤ epsilon) (hε_lt_one : epsilon < 1)
    (halpha : 1 < alpha) :
    rho.hypothesisTestingRelativeEntropyPSDE sigma epsilon ≤
      rho.sandwichedRenyiPSDReferenceE sigma hsigma alpha +
        ((alpha / (alpha - 1) * log2 (1 / (1 - epsilon)) : ℝ) : EReal) := by
  by_cases hSupport : Matrix.Supports rho.matrix sigma
  · have hfinite :
        rho.hypothesisTestingRelativeEntropyPSDE sigma epsilon ≤
          ((rho.sandwichedRenyiPSDReferenceHighAlphaFinite sigma hsigma alpha +
            alpha / (alpha - 1) * log2 (1 / (1 - epsilon)) : ℝ) : EReal) :=
      hypothesisTestingRelativeEntropyPSDE_le_of_effect_rpow_lower_bound
        (rho := rho) (sigma := sigma) (epsilon := epsilon)
        (C := rho.sandwichedRenyiPSDReferenceHighAlphaFinite sigma hsigma alpha +
          alpha / (alpha - 1) * log2 (1 / (1 - epsilon)))
        hε_nonneg
        (fun Lambda =>
          typeIIErrorPSD_rpow_lower_bound_of_sandwichedRenyi
            rho hsigma hε_lt_one halpha hSupport Lambda)
    rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt rho hsigma halpha,
      sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
        rho hsigma alpha hSupport]
    simpa [EReal.coe_add] using hfinite
  · exact
      hypothesisTestingRelativeEntropyPSDE_le_sandwichedRenyiPSDReferenceE_add_of_not_supports
        rho hsigma halpha hSupport

end State

end

end QIT
