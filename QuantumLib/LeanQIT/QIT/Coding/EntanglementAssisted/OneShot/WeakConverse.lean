/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.OneShot.Converse
public import QIT.HypothesisTesting.SandwichedComparison
public import QIT.Information.Entropy.MutualInformationDPI
public import QIT.Information.Entropy.EntropyTensorPower

/-!
# Entanglement-assisted weak-converse bridge

This module records the weak-converse one-shot upper-bound surface for
entanglement-assisted classical communication.

The Khatri--Wilde source proves the one-shot upper bound

`C_EA^ε(N) <= (I(N) + h₂(ε)) / (1 - ε)`

by combining the hypothesis-testing converse with a weak-converse comparison
from hypothesis-testing mutual information to the ordinary channel mutual
information
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:411-427].

The source-level comparison ultimately depends on the finite-blocklength
entropy comparison from the source's hypothesis-testing-to-relative-entropy
proposition.  The current Lean API does not yet contain the required
Fano/relative-entropy bridge, so the channel-level comparison is kept as an
explicit, named hypothesis.  The final capacity assembly from that comparison
is fully proved here and reuses the hypothesis-testing converse.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace EntanglementAssistedWeakConverse

/-- Binary entropy `h₂(ε) = -ε log₂ ε - (1 - ε) log₂(1 - ε)`.

This is intentionally local to the entanglement-assisted weak-converse surface;
a global entropy API can later reuse or replace it once the surrounding binary
entropy lemmas are formalized. -/
def binaryEntropy (ε : ℝ) : ℝ :=
  -xlog2 ε - xlog2 (1 - ε)

/-- `-log₂ q ≤ C` is equivalent to the exponential lower bound
`2^{-C} ≤ q` on positive `q`. -/
private theorem rpow_two_neg_le_of_neg_log2_le {q C : ℝ} (hq : 0 < q)
    (h : -log2 q ≤ C) :
    Real.rpow 2 (-C) ≤ q := by
  have hexp : -C ≤ log2 q := by linarith
  have hpow :=
    Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ))
      (by norm_num : (1 : ℝ) ≤ 2) hexp
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpow_log : Real.rpow 2 (log2 q) = q := by
    apply Real.log_injOn_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hq
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    unfold log2
    field_simp [hlog2_pos.ne']
  exact hpow.trans_eq hpow_log

/-- A binary measurement of a PSD matrix is the real diagonal matrix of its
Born-rule weights.  This is kept local to the weak-converse proof because the
same statement is also used internally in the sandwiched comparison route. -/
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

/-- Base-2 version of the `log 0 = 0` functional-calculus scalar. -/
private def logZero2 (x : ℝ) : ℝ :=
  if x = 0 then 0 else log2 x

private theorem logZero_div_log2 (x : ℝ) :
    (if x = 0 then 0 else Real.log x) / Real.log 2 = logZero2 x := by
  by_cases hx : x = 0
  · simp [logZero2, hx]
  · simp [logZero2, hx, log2]

end EntanglementAssistedWeakConverse

namespace HypothesisTestingEffect

variable {rho sigma : State a} {epsilon : ℝ}

/-- Reject probability is `1` minus accept probability for the binary POVM
induced by a feasible effect. -/
theorem rejectProbability_eq_one_sub_accept
    (Lambda : HypothesisTestingEffect rho epsilon) :
    effectAcceptProbability rho (1 - Lambda.effect) =
      1 - effectAcceptProbability rho Lambda.effect := by
  unfold effectAcceptProbability
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_one, rho.trace_eq_one]
  simp

/-- Reject probability is `1` minus accept probability for any normalized state,
not only for the state used to define feasibility of the effect. -/
theorem rejectProbabilityState_eq_one_sub_accept
    (Lambda : HypothesisTestingEffect rho epsilon) (tau : State a) :
    effectAcceptProbability tau (1 - Lambda.effect) =
      1 - effectAcceptProbability tau Lambda.effect := by
  unfold effectAcceptProbability
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_one, tau.trace_eq_one]
  simp

/-- Type-II error is a probability and hence at most one. -/
theorem typeIIError_le_one (Lambda : HypothesisTestingEffect rho epsilon)
    (sigma : State a) :
    Lambda.typeIIError sigma ≤ 1 := by
  have hprob := Lambda.toBinaryHypothesisTest.prob_le_one sigma true
  have hprob_real : ((Lambda.toBinaryHypothesisTest.prob sigma true : ℝ)) ≤ 1 := by
    exact_mod_cast hprob
  change ((Lambda.toBinaryHypothesisTest.acceptProb sigma : ℝ)) ≤ 1 at hprob_real
  change ((Lambda.toBinaryHypothesisTest.typeIIError sigma : ℝ)) ≤ 1 at hprob_real
  rw [Lambda.toBinaryHypothesisTest_typeIIError sigma] at hprob_real
  exact hprob_real

/-- The PSD-reference type-II error is monotone under the source rescaling that
saturates the type-I constraint. -/
theorem scaleToAcceptEquality_typeIIErrorPSD_le
    (Lambda : HypothesisTestingEffect rho epsilon) (hε_lt_one : epsilon < 1)
    {sigma : CMatrix a} (hsigma : sigma.PosSemidef) :
    (Lambda.scaleToAcceptEquality hε_lt_one).typeIIErrorPSD sigma ≤
      Lambda.typeIIErrorPSD sigma := by
  have hcoef1 :=
    one_minus_epsilon_div_accept_le_one Lambda hε_lt_one
  have htype_nonneg : 0 ≤ Lambda.typeIIErrorPSD sigma :=
    Lambda.typeIIErrorPSD_nonneg hsigma
  unfold typeIIErrorPSD
  simp [scaleToAcceptEquality, Matrix.trace_smul]
  exact mul_le_of_le_one_left htype_nonneg hcoef1

end HypothesisTestingEffect

namespace State

/-- Finite trace-log PSD-reference relative entropy rewritten on the original
state/reference pair, using the `log 0 = 0` functional calculus. -/
private theorem relativeEntropyPSDReferenceTraceLogFinite_eq_entropy_traceLog
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma) :
    relativeEntropyPSDReferenceTraceLogFinite rho sigma hsigma hSupport =
      -rho.vonNeumann -
        (((rho.matrix *
          cfc (fun x : ℝ => if x = 0 then 0 else Real.log x) sigma).trace).re /
            Real.log 2) := by
  have hEntropy :
      (_root_.QIT.psdSupportCompressedState rho hsigma hSupport).vonNeumann =
        rho.vonNeumann :=
    State.vonNeumann_psdSupportCompressedState_eq rho hsigma hSupport
  have hTrace :
      ((psdSupportCompress sigma hsigma rho.matrix *
        State.psdLog (psdSupportCompress sigma hsigma sigma)
          (psdSupportCompress_self_posDef sigma hsigma)).trace).re =
        ((rho.matrix *
          cfc (fun x : ℝ => if x = 0 then 0 else Real.log x) sigma).trace).re :=
    trace_mul_psdSupportLog_eq_trace_mul_cfc_logZero rho hsigma hSupport
  simp [relativeEntropyPSDReferenceTraceLogFinite, hEntropy, hTrace]

/-- Binary measured relative entropy lower bound used in the
Khatri--Wilde `prop-hypo_to_rel_ent` route.

For a saturated test `Tr[Λρ] = 1 - ε`, the measured first hypothesis is the
Bernoulli distribution `(1 - ε, ε)`.  The second hypothesis has accept
probability `q = Tr[Λσ]`.  Computing the diagonal trace-log expression gives
`D(meas ρ || meas σ) >= (1 - ε) * (-log₂ q) - h₂(ε)`. -/
private theorem binaryMeasured_traceLogE_lower_of_saturated
    (rho sigma : State a) {epsilon : ℝ}
    (Lambda : HypothesisTestingEffect rho epsilon)
    (hε_nonneg : 0 ≤ epsilon) (hε_lt_one : epsilon < 1)
    (haccept : effectAcceptProbability rho Lambda.effect = 1 - epsilon)
    (hSupport : Matrix.Supports rho.matrix sigma.matrix) :
    (((1 - epsilon) * (-log2 (Lambda.typeIIError sigma)) -
        EntanglementAssistedWeakConverse.binaryEntropy epsilon : ℝ) : EReal) ≤
      relativeEntropyPSDReferenceTraceLogE
        ((Channel.measure Lambda.toBinaryHypothesisTest).applyState rho)
        ((Channel.measure Lambda.toBinaryHypothesisTest).map sigma.matrix)
        ((Channel.measure Lambda.toBinaryHypothesisTest).mapsPositive
          sigma.matrix sigma.pos) := by
  classical
  let Phi : Channel a Bool := Channel.measure Lambda.toBinaryHypothesisTest
  let p : Bool → ℝ := fun b => if b then 1 - epsilon else epsilon
  let q : ℝ := Lambda.typeIIError sigma
  let qdist : Bool → ℝ := fun b => if b then q else 1 - q
  have hq_pos : 0 < q := by
    have hpsd_pos :
        0 < Lambda.typeIIErrorPSD sigma.matrix :=
      Lambda.typeIIErrorPSD_pos_of_supports sigma.pos hSupport hε_lt_one
    simpa [q, Lambda.typeIIErrorPSD_eq_state sigma] using hpsd_pos
  have hq_le_one : q ≤ 1 := by
    simpa [q] using Lambda.typeIIError_le_one sigma
  have haccept_trace :
      ((rho.matrix * Lambda.effect).trace).re = 1 - epsilon := by
    simpa [effectAcceptProbability] using haccept
  have hreject_trace :
      ((rho.matrix * (1 - Lambda.effect)).trace).re = epsilon := by
    have h :=
      Lambda.rejectProbability_eq_one_sub_accept
    rw [haccept] at h
    simpa [effectAcceptProbability] using h
  have hsigma_reject_trace :
      ((sigma.matrix * (1 - Lambda.effect)).trace).re =
        1 - ((sigma.matrix * Lambda.effect).trace).re := by
    have h :=
      Lambda.rejectProbabilityState_eq_one_sub_accept sigma
    simpa [effectAcceptProbability] using h
  have hPhiRho :
      (Phi.applyState rho).matrix =
        Matrix.diagonal (fun b : Bool => ((p b : ℝ) : ℂ)) := by
    change Phi.map rho.matrix = _
    rw [EntanglementAssistedWeakConverse.measurement_map_eq_diagonal_re
      Lambda.toBinaryHypothesisTest rho.pos]
    ext i j
    cases i <;> cases j <;>
      simp [p, HypothesisTestingEffect.toBinaryHypothesisTest,
        haccept_trace, hreject_trace]
  have hPhiSigma :
      Phi.map sigma.matrix =
        Matrix.diagonal (fun b : Bool => ((qdist b : ℝ) : ℂ)) := by
    rw [EntanglementAssistedWeakConverse.measurement_map_eq_diagonal_re
      Lambda.toBinaryHypothesisTest sigma.pos]
    ext i j
    cases i <;> cases j <;>
      simp [qdist, q, HypothesisTestingEffect.toBinaryHypothesisTest,
        effectTypeIIError, effectAcceptProbability, hsigma_reject_trace]
  have hOutSupport :
      Matrix.Supports (Phi.applyState rho).matrix (Phi.map sigma.matrix) :=
    State.channel_map_supports Phi sigma.pos hSupport
  have hEntropy :
      (Phi.applyState rho).vonNeumann =
        -(∑ b : Bool, xlog2 (p b)) :=
    State.vonNeumann_eq_neg_sum_xlog2_of_diagonal
      (Phi.applyState rho) p hPhiRho
  have hCfc :
      cfc (fun x : ℝ => if x = 0 then 0 else Real.log x) (Phi.map sigma.matrix) =
        Matrix.diagonal
          (fun b : Bool =>
            (((if qdist b = 0 then 0 else Real.log (qdist b) : ℝ)) : ℂ)) := by
    rw [hPhiSigma]
    exact cfc_diagonal_ofReal qdist
      (fun x : ℝ => if x = 0 then 0 else Real.log x)
  have hTrace :
      (((Phi.applyState rho).matrix *
        cfc (fun x : ℝ => if x = 0 then 0 else Real.log x)
          (Phi.map sigma.matrix)).trace).re / Real.log 2 =
        (1 - epsilon) * log2 q +
          epsilon * EntanglementAssistedWeakConverse.logZero2 (1 - q) := by
    rw [hPhiRho, hCfc]
    have hq_ne : q ≠ 0 := ne_of_gt hq_pos
    simp [p, qdist, Matrix.trace, Matrix.mul_apply, Matrix.diagonal,
      EntanglementAssistedWeakConverse.logZero2, log2, hq_ne]
    by_cases hqcompl : 1 - q = 0
    · simp [hqcompl]
      ring_nf
    · simp [hqcompl]
      ring_nf
  have hlog_compl_nonpos :
      EntanglementAssistedWeakConverse.logZero2 (1 - q) ≤ 0 := by
    have hcompl_nonneg : 0 ≤ 1 - q := sub_nonneg.mpr hq_le_one
    have hcompl_le_one : 1 - q ≤ 1 := by linarith [le_of_lt hq_pos]
    by_cases hzero : 1 - q = 0
    · simp [EntanglementAssistedWeakConverse.logZero2, hzero]
    · have hlog_nonpos :
          Real.log (1 - q) / Real.log 2 ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg
          (Real.log_nonpos hcompl_nonneg hcompl_le_one)
          (le_of_lt (Real.log_pos one_lt_two))
      simpa [EntanglementAssistedWeakConverse.logZero2, hzero, log2] using hlog_nonpos
  have hreal :
      (1 - epsilon) * (-log2 q) -
          EntanglementAssistedWeakConverse.binaryEntropy epsilon ≤
        relativeEntropyPSDReferenceTraceLogFinite
          (Phi.applyState rho) (Phi.map sigma.matrix)
          (Phi.mapsPositive sigma.matrix sigma.pos) hOutSupport := by
    rw [relativeEntropyPSDReferenceTraceLogFinite_eq_entropy_traceLog
      (Phi.applyState rho) (Phi.mapsPositive sigma.matrix sigma.pos)
      hOutSupport]
    rw [hEntropy, hTrace]
    have hdrop :
        0 ≤ -epsilon *
          EntanglementAssistedWeakConverse.logZero2 (1 - q) := by
      exact mul_nonneg_of_nonpos_of_nonpos
        (neg_nonpos.mpr hε_nonneg) hlog_compl_nonpos
    unfold EntanglementAssistedWeakConverse.binaryEntropy
    rw [Fintype.sum_bool]
    simp [p]
    nlinarith
  rw [relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports
    (Phi.applyState rho) (Phi.mapsPositive sigma.matrix sigma.pos) hOutSupport]
  exact EReal.coe_le_coe_iff.mpr hreal

/-- State-level weak-converse comparison from hypothesis-testing mutual
information to ordinary mutual information plus the binary-entropy penalty.

This is the local formal surface for the source comparison
`I_H^ε(A;B)_ρ <= (I(A;B)_ρ + h₂(ε)) / (1 - ε)`. -/
def HypothesisTestingMutualInformationWeakConverseBound
    (rhoAB : State (Prod a b)) (ε : ℝ) : Prop :=
  rhoAB.hypothesisTestingMutualInformation ε ≤
    ((mutualInformation rhoAB +
        EntanglementAssistedWeakConverse.binaryEntropy ε) / (1 - ε) : EReal)

/-- Barred hypothesis-testing relative-entropy comparison at the product of
the marginals.

This is the source-shaped remaining comparison behind the state-level
weak-converse bound: instantiate the hypothesis-testing-to-relative-entropy
comparison of
[KhatriWilde2024Principles, Chapters/entropies.tex:6952-6984] at
`σ = ρ_A ⊗ ρ_B`, where the trace-normalization term vanishes, and identify the
relative entropy with `I(A;B)_ρ`. -/
def HypothesisTestingRelativeEntropyMarginalsWeakConverseBound
    (rhoAB : State (Prod a b)) (ε : ℝ) : Prop :=
  rhoAB.hypothesisTestingRelativeEntropy
      (rhoAB.marginalA.prod rhoAB.marginalB) ε ≤
    ((mutualInformation rhoAB +
        EntanglementAssistedWeakConverse.binaryEntropy ε) / (1 - ε) : EReal)

/-- Product-marginal hypothesis-testing relative entropy is bounded by the
ordinary mutual information plus the binary-entropy weak-converse penalty.

This is the finite-dimensional Lean realization of the source comparison
`prop-hypo_to_rel_ent`, specialized to
`σ_AB = ρ_A ⊗ ρ_B`.  The proof uses saturated tests, binary measurement data
processing, and the trace-log identity
`D(ρ_AB || ρ_A ⊗ ρ_B) = I(A;B)_ρ`. -/
theorem hypothesisTestingRelativeEntropyMarginalsWeakConverseBound
    (rhoAB : State (Prod a b)) {ε : ℝ}
    (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1) :
    rhoAB.HypothesisTestingRelativeEntropyMarginalsWeakConverseBound ε := by
  classical
  let sigma : State (Prod a b) := rhoAB.marginalA.prod rhoAB.marginalB
  let C : ℝ :=
    (mutualInformation rhoAB +
        EntanglementAssistedWeakConverse.binaryEntropy ε) / (1 - ε)
  have hSupport : Matrix.Supports rhoAB.matrix sigma.matrix := by
    simpa [sigma] using rhoAB.matrix_supports_prod_marginals
  have hRelEq :
      rhoAB.relativeEntropy sigma =
        (mutualInformation rhoAB : EReal) := by
    simpa [sigma] using
      State.relativeEntropy_prod_marginals_eq_mutualInformation rhoAB
  have hlower :
      ∀ Lambda : HypothesisTestingEffect rhoAB ε,
        Real.rpow 2 (-C) ≤ Lambda.typeIIErrorPSD sigma.matrix := by
    intro Lambda
    let Lambda' := Lambda.scaleToAcceptEquality hε_lt_one
    let q : ℝ := Lambda'.typeIIError sigma
    have hq_pos : 0 < q := by
      have hpsd_pos :
          0 < Lambda'.typeIIErrorPSD sigma.matrix :=
        Lambda'.typeIIErrorPSD_pos_of_supports sigma.pos hSupport hε_lt_one
      simpa [q, Lambda'.typeIIErrorPSD_eq_state sigma] using hpsd_pos
    have hmeasured :
        (((1 - ε) * (-log2 q) -
            EntanglementAssistedWeakConverse.binaryEntropy ε : ℝ) : EReal) ≤
          relativeEntropyPSDReferenceTraceLogE
            ((Channel.measure Lambda'.toBinaryHypothesisTest).applyState rhoAB)
            ((Channel.measure Lambda'.toBinaryHypothesisTest).map sigma.matrix)
            ((Channel.measure Lambda'.toBinaryHypothesisTest).mapsPositive
              sigma.matrix sigma.pos) := by
      simpa [q] using
        binaryMeasured_traceLogE_lower_of_saturated rhoAB sigma Lambda'
          hε_nonneg hε_lt_one
          (Lambda.scaleToAcceptEquality_accept_eq hε_lt_one) hSupport
    have hdpi :
        relativeEntropyPSDReferenceTraceLogE
            ((Channel.measure Lambda'.toBinaryHypothesisTest).applyState rhoAB)
            ((Channel.measure Lambda'.toBinaryHypothesisTest).map sigma.matrix)
            ((Channel.measure Lambda'.toBinaryHypothesisTest).mapsPositive
              sigma.matrix sigma.pos) ≤
          rhoAB.relativeEntropy sigma := by
      have hDPI :=
        State.relativeEntropy_dataProcessing_channel_ge
          rhoAB sigma (Channel.measure Lambda'.toBinaryHypothesisTest)
      simpa [State.relativeEntropy, Channel.applyState] using hDPI
    have hE :
        (((1 - ε) * (-log2 q) -
            EntanglementAssistedWeakConverse.binaryEntropy ε : ℝ) : EReal) ≤
          (mutualInformation rhoAB : EReal) := by
      exact hmeasured.trans (hdpi.trans_eq hRelEq)
    have hreal :
        (1 - ε) * (-log2 q) -
            EntanglementAssistedWeakConverse.binaryEntropy ε ≤
          mutualInformation rhoAB :=
      EReal.coe_le_coe_iff.mp hE
    have hden_pos : 0 < 1 - ε := sub_pos.mpr hε_lt_one
    have hneglog :
        -log2 q ≤ C := by
      have hmul :
          (1 - ε) * (-log2 q) ≤
            mutualInformation rhoAB +
              EntanglementAssistedWeakConverse.binaryEntropy ε := by
        linarith
      exact (le_div_iff₀ hden_pos).mpr (by
        simpa [mul_comm] using hmul)
    have hrpow :
        Real.rpow 2 (-C) ≤ Lambda'.typeIIErrorPSD sigma.matrix := by
      simpa [q, Lambda'.typeIIErrorPSD_eq_state sigma] using
        EntanglementAssistedWeakConverse.rpow_two_neg_le_of_neg_log2_le hq_pos hneglog
    exact hrpow.trans
      (Lambda.scaleToAcceptEquality_typeIIErrorPSD_le hε_lt_one sigma.pos)
  have hpsd :
      rhoAB.hypothesisTestingRelativeEntropyPSDE sigma.matrix ε ≤ (C : EReal) :=
    State.hypothesisTestingRelativeEntropyPSDE_le_of_effect_rpow_lower_bound
      (rho := rhoAB) (sigma := sigma.matrix) (epsilon := ε) (C := C)
      hε_nonneg hlower
  simpa [HypothesisTestingRelativeEntropyMarginalsWeakConverseBound, sigma, C,
    State.hypothesisTestingRelativeEntropyPSDE_eq_state] using hpsd

/-- Optimizing hypothesis-testing mutual information over Bob-side states is
bounded by the barred choice `σ_B = ρ_B`. -/
theorem hypothesisTestingMutualInformation_le_relativeEntropy_marginals
    (rhoAB : State (Prod a b)) (ε : ℝ) :
    rhoAB.hypothesisTestingMutualInformation ε ≤
      rhoAB.hypothesisTestingRelativeEntropy
        (rhoAB.marginalA.prod rhoAB.marginalB) ε := by
  rw [hypothesisTestingMutualInformation_eq_sInf]
  exact sInf_le ⟨rhoAB.marginalB, rfl⟩

/-- Reduce the state-level weak-converse comparison to the barred
hypothesis-testing-relative-entropy comparison at the marginal product. -/
theorem hypothesisTestingMutualInformationWeakConverseBound_of_relativeEntropy_marginals
    (rhoAB : State (Prod a b)) {ε : ℝ}
    (hrel : rhoAB.HypothesisTestingRelativeEntropyMarginalsWeakConverseBound ε) :
    rhoAB.HypothesisTestingMutualInformationWeakConverseBound ε :=
  (rhoAB.hypothesisTestingMutualInformation_le_relativeEntropy_marginals ε).trans
    hrel

/-- State-level weak-converse comparison from optimized hypothesis-testing
mutual information to ordinary mutual information. -/
theorem hypothesisTestingMutualInformationWeakConverseBound
    (rhoAB : State (Prod a b)) {ε : ℝ}
    (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1) :
    rhoAB.HypothesisTestingMutualInformationWeakConverseBound ε :=
  rhoAB.hypothesisTestingMutualInformationWeakConverseBound_of_relativeEntropy_marginals
    (rhoAB.hypothesisTestingRelativeEntropyMarginalsWeakConverseBound
      hε_nonneg hε_lt_one)

end State

namespace Channel

variable (N : Channel a b)

/-- Real-valued weak-converse upper-bound expression
`(I(N) + h₂(ε)) / (1 - ε)`. -/
def entanglementAssistedWeakConverseBound (ε : ℝ) : ℝ :=
  (N.entanglementAssistedInformation +
      EntanglementAssistedWeakConverse.binaryEntropy ε) / (1 - ε)

/-- Channel-level weak-converse comparison needed for Khatri--Wilde's
one-shot upper-bound theorem.

This is the remaining mathematical comparison: the optimized
hypothesis-testing mutual information is bounded by the ordinary
entanglement-assisted mutual-information objective plus the binary-entropy
penalty. -/
def HypothesisTestingMutualInformationWeakConverseBound (ε : ℝ) : Prop :=
  N.hypothesisTestingMutualInformation ε ≤
    (N.entanglementAssistedWeakConverseBound ε : EReal)

/-- Lift the state-level weak-converse comparison for every pure
input-reference output state through the channel supremum. -/
theorem hypothesisTestingMutualInformationWeakConverseBound_of_state
    [Nonempty a] {ε : ℝ} (hε_lt_one : ε < 1)
    (hstate :
      ∀ ψ : PureVector (Prod a a),
        State.HypothesisTestingMutualInformationWeakConverseBound
          (N.hypothesisTestingOutputState ψ) ε) :
    N.HypothesisTestingMutualInformationWeakConverseBound ε := by
  rw [HypothesisTestingMutualInformationWeakConverseBound,
    hypothesisTestingMutualInformation_eq_sSup]
  refine sSup_le ?_
  intro value hvalue
  rcases hvalue with ⟨ψ, rfl⟩
  have hstateψ :=
    hstate ψ
  have hmi :
      mutualInformation (N.hypothesisTestingOutputState ψ) ≤
        N.entanglementAssistedInformation := by
    simpa [Channel.hypothesisTestingOutputState,
      Channel.entanglementAssistedOutputState,
      Channel.entanglementAssistedMutualInformation] using
      N.entanglementAssistedMutualInformation_le_information ψ
  have hden : 0 ≤ 1 - ε := sub_nonneg.mpr (le_of_lt hε_lt_one)
  have hreal :
      (mutualInformation (N.hypothesisTestingOutputState ψ) +
            EntanglementAssistedWeakConverse.binaryEntropy ε) / (1 - ε) ≤
        N.entanglementAssistedWeakConverseBound ε := by
    unfold entanglementAssistedWeakConverseBound
    exact div_le_div_of_nonneg_right (add_le_add hmi le_rfl) hden
  exact hstateψ.trans (EReal.coe_le_coe_iff.mpr hreal)

/-- Channel-level weak-converse comparison
`I_H^ε(N) <= (I(N) + h₂(ε)) / (1 - ε)`. -/
theorem hypothesisTestingMutualInformationWeakConverseBound
    [Nonempty a] {ε : ℝ} (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1) :
    N.HypothesisTestingMutualInformationWeakConverseBound ε :=
  N.hypothesisTestingMutualInformationWeakConverseBound_of_state hε_lt_one
    (fun ψ =>
      State.hypothesisTestingMutualInformationWeakConverseBound
        (N.hypothesisTestingOutputState ψ) hε_nonneg hε_lt_one)

/--
Algebraic bridge from the hypothesis-testing one-shot converse and the
channel-level weak-converse comparison to the Khatri--Wilde one-shot weak
converse upper bound.

This is the final assembly step of
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:411-427].  The comparison
hypothesis represents the still-separate entropy/Fano-to-relative-entropy
ingredient from the same source development.
-/
theorem oneShotEntanglementAssistedClassicalCapacityE_le_weakConverseBound_of_comparison
    {ε : ℝ} (hε_nonneg : 0 ≤ ε) (_hε_lt_one : ε < 1)
    (hcmp : N.HypothesisTestingMutualInformationWeakConverseBound ε) :
    N.oneShotEntanglementAssistedClassicalCapacityE ε ≤
      (N.entanglementAssistedWeakConverseBound ε : EReal) :=
  (N.oneShotEntanglementAssistedClassicalCapacityE_le_hypothesisTestingMutualInformation
    hε_nonneg).trans hcmp

/-- One-shot entanglement-assisted weak converse upper bound in capacity form.

This removes the comparison hypothesis from
`oneShotEntanglementAssistedClassicalCapacityE_le_weakConverseBound_of_comparison`
by using the proved hypothesis-testing-to-relative-entropy weak-converse
comparison. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_le_weakConverseBound
    [Nonempty a] {ε : ℝ} (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1) :
    N.oneShotEntanglementAssistedClassicalCapacityE ε ≤
      (N.entanglementAssistedWeakConverseBound ε : EReal) :=
  N.oneShotEntanglementAssistedClassicalCapacityE_le_weakConverseBound_of_comparison
    hε_nonneg hε_lt_one
    (N.hypothesisTestingMutualInformationWeakConverseBound hε_nonneg hε_lt_one)

end Channel

namespace EntanglementAssistedClassicalCode

variable {N : Channel a b}
variable {M : Type w} [Fintype M] [DecidableEq M] [Nonempty M]
variable {EA : Type x} [Fintype EA] [DecidableEq EA]
variable {EB : Type y} [Fintype EB] [DecidableEq EB]

/-- Per-code assembly form of the weak-converse upper bound, assuming the
channel-level weak-converse comparison. -/
theorem log_card_le_channel_entanglementAssistedWeakConverseBoundE_of_comparison
    (C : EntanglementAssistedClassicalCode N 1 M EA EB)
    {ε : ℝ} (hε_nonneg : 0 ≤ ε)
    (hC : C.maxErrorAtMost ε)
    (hcmp : N.HypothesisTestingMutualInformationWeakConverseBound ε) :
    (log2 (Fintype.card M : ℝ) : EReal) ≤
      (N.entanglementAssistedWeakConverseBound ε : EReal) :=
  (C.log_card_le_channel_hypothesisTestingMutualInformation hε_nonneg hC).trans
    hcmp

/-- Real-valued per-code assembly form of the weak-converse upper bound,
assuming the channel-level weak-converse comparison. -/
theorem log_card_le_channel_entanglementAssistedWeakConverseBound_of_comparison
    (C : EntanglementAssistedClassicalCode N 1 M EA EB)
    {ε : ℝ} (hε_nonneg : 0 ≤ ε)
    (hC : C.maxErrorAtMost ε)
    (hcmp : N.HypothesisTestingMutualInformationWeakConverseBound ε) :
    log2 (Fintype.card M : ℝ) ≤
      N.entanglementAssistedWeakConverseBound ε :=
  EReal.coe_le_coe_iff.mp
    (C.log_card_le_channel_entanglementAssistedWeakConverseBoundE_of_comparison
      hε_nonneg hC hcmp)

/-- Per-code weak-converse upper bound with the comparison theorem proved
internally. -/
theorem log_card_le_channel_entanglementAssistedWeakConverseBoundE
    [Nonempty a]
    (C : EntanglementAssistedClassicalCode N 1 M EA EB)
    {ε : ℝ} (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1)
    (hC : C.maxErrorAtMost ε) :
    (log2 (Fintype.card M : ℝ) : EReal) ≤
      (N.entanglementAssistedWeakConverseBound ε : EReal) :=
  C.log_card_le_channel_entanglementAssistedWeakConverseBoundE_of_comparison
    hε_nonneg hC
    (N.hypothesisTestingMutualInformationWeakConverseBound hε_nonneg hε_lt_one)

/-- Real-valued per-code weak-converse upper bound with the comparison theorem
proved internally. -/
theorem log_card_le_channel_entanglementAssistedWeakConverseBound
    [Nonempty a]
    (C : EntanglementAssistedClassicalCode N 1 M EA EB)
    {ε : ℝ} (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1)
    (hC : C.maxErrorAtMost ε) :
    log2 (Fintype.card M : ℝ) ≤
      N.entanglementAssistedWeakConverseBound ε :=
  EReal.coe_le_coe_iff.mp
    (C.log_card_le_channel_entanglementAssistedWeakConverseBoundE
      hε_nonneg hε_lt_one hC)

end EntanglementAssistedClassicalCode

end

end QIT
