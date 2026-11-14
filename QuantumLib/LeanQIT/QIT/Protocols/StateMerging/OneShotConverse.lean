/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Protocols.StateMerging.InputSource
public import QIT.Protocols.StateMerging.RecordedOutcome
public import QIT.Protocols.LOCC.ConditionalMinEntropy
public import QIT.Protocols.LOCC.SmoothConditionalMinEntropy

/-!
# One-shot smooth-min-entropy converse for quantum state merging

This module assembles Berta's one-shot converse for the concrete block
protocol.  The smoothing radius is derived from the protocol's actual
fidelity error, and the rate form uses only the canonical finite-radius
conditions.
-/

@[expose] public section

namespace QIT

universe u v w x y z p q

noncomputable section

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable {psi : PureVector (Prod (Prod a b) r)} {n : Nat}
variable {kA : Type x} {kB : Type y} {lA : Type z} {lB : Type p}
variable {outcome : Type q}
variable [Fintype kA] [DecidableEq kA] [Nonempty kA]
variable [Fintype kB] [DecidableEq kB]
variable [Fintype lA] [DecidableEq lA] [Nonempty lA]
variable [Fintype lB] [DecidableEq lB]
variable [Fintype outcome] [DecidableEq outcome] [Nonempty outcome]

namespace StateMergingBlockProtocol

variable (C : StateMergingBlockProtocol psi n kA kB lA lB outcome)

/-- The purified-distance radius supplied by the protocol's actual fidelity
error and the normalized trace-distance-to-purified-distance conversion. -/
def oneShotConversePurifiedRadius : Real :=
  Real.sqrt
    (2 * Real.sqrt C.fidelityError - (Real.sqrt C.fidelityError) ^ 2)

theorem oneShotConversePurifiedRadius_nonneg :
    0 <= C.oneShotConversePurifiedRadius := by
  exact Real.sqrt_nonneg _

private theorem sourceReferenceState_localConverseInputPureVector :
    FiniteInstrument.sourceReferenceState C.localConverseInputPureVector =
      C.converseInputPureVector.state.marginalA := by
  apply State.ext
  ext i j
  rfl

private theorem recordedOutcomeState_eq_originalRecordedOutcomeState :
    C.recordedOutcomeState = C.originalRecordedOutcomeState := by
  rfl

private theorem idealRecordedConditioningEnsemble_states_eq_sourceReference
    (i : C.recordedOutcomeIndex) :
    C.idealRecordedConditioningEnsemble.states i =
      (stateMergingBlockSource psi n).state.marginalB := by
  rfl

/-- Berta's one-shot smooth-min-entropy converse for a concrete physical
state-merging block protocol. -/
theorem oneShotSmoothMinEntropy_converse
    (hradius : C.oneShotConversePurifiedRadius < 1) :
    log2 (Fintype.card lA : Real) <=
      log2 (Fintype.card kA : Real) +
        psi.state.marginalAC.tensorPowerSubnormalizedSmoothConditionalMinEntropy
          C.oneShotConversePurifiedRadius n
          C.oneShotConversePurifiedRadius_nonneg hradius := by
  letI : DecidableEq (TensorPower a n) := tensorPowerDecidableEq n
  letI : DecidableEq (TensorPower b n) := tensorPowerDecidableEq n
  letI : DecidableEq (TensorPower r n) := tensorPowerDecidableEq n
  letI : DecidableEq C.recordedOutcomeIndex := Classical.decEq _
  letI : Nonempty a := Nonempty.map (fun i ↦ i.1.1) psi.state.nonempty
  letI : Nonempty r := Nonempty.map (fun i ↦ i.2) psi.state.nonempty
  have hballState :
      C.recordedOutcomeState.purifiedBall C.oneShotConversePurifiedRadius
        C.idealRecordedOutcomeState := by
    simpa only [oneShotConversePurifiedRadius] using
      C.recordedOutcomeState_purifiedBall
  have hball :
      C.recordedOutcomeState.toSubnormalized.purifiedBall
        C.oneShotConversePurifiedRadius
        C.idealRecordedOutcomeState.toSubnormalized :=
    (State.purifiedBall_iff_toSubnormalized_purifiedBall
      C.recordedOutcomeState C.idealRecordedOutcomeState _).mp hballState
  have hballOriginal :
      C.originalRecordedOutcomeState.toSubnormalized.purifiedBall
        C.oneShotConversePurifiedRadius
        C.idealRecordedOutcomeState.toSubnormalized := by
    simpa only [C.recordedOutcomeState_eq_originalRecordedOutcomeState] using hball
  change
    (C.locc.aliceInstrument.recordedSourceReferenceState
      C.localConverseInputPureVector).toSubnormalized.purifiedBall
        C.oneShotConversePurifiedRadius
        C.idealRecordedOutcomeState.toSubnormalized at hballOriginal
  let sigmaR : State (TensorPower r n) :=
    (stateMergingBlockSource psi n).state.marginalB
  have hfixedReferenceState :
      C.locc.aliceInstrument.recordedFixedReferenceState
          C.localConverseInputPureVector sigmaR =
        C.idealRecordedConditioningState := by
    apply State.ext
    ext i j
    rfl
  have hidealFixed :
      C.idealRecordedOutcomeState =
        C.locc.aliceInstrument.recordedMaximallyMixedFixedReferenceState
          C.localConverseInputPureVector sigmaR := by
    rw [C.idealRecordedOutcomeState_eq_maximallyMixed_prod,
      FiniteInstrument.recordedMaximallyMixedFixedReferenceState,
      hfixedReferenceState]
  have hballFixed :
      (C.locc.aliceInstrument.recordedSourceReferenceState
        C.localConverseInputPureVector).toSubnormalized.purifiedBall
          C.oneShotConversePurifiedRadius
          (C.locc.aliceInstrument.recordedMaximallyMixedFixedReferenceState
            C.localConverseInputPureVector sigmaR).toSubnormalized := by
    rw [← hidealFixed]
    exact hballOriginal
  obtain ⟨h', hcandInput, hlog⟩ :=
    C.locc.aliceInstrument.recordedFixedReferenceCandidate_compress
      C.localConverseInputPureVector sigmaR hradius hballFixed
  have hcandConverse :
      SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw
        (a := Prod (TensorPower a n) kA)
        C.converseInputPureVector.state.marginalA.toSubnormalized
        C.oneShotConversePurifiedRadius h' := by
    simpa only [C.sourceReferenceState_localConverseInputPureVector] using hcandInput
  have hsourceTrace :
      C.oneShotConversePurifiedRadius <
        Real.sqrt
          C.converseInputPureVector.state.marginalA.toSubnormalized.matrix.trace.re := by
    rw [State.toSubnormalized_trace]
    simpa using hradius
  have hcandidateLe :
      h' <= C.converseInputPureVector.state.marginalA.toSubnormalized.smoothConditionalMinEntropy
          C.oneShotConversePurifiedRadius
          C.oneShotConversePurifiedRadius_nonneg hsourceTrace :=
    SubnormalizedState.le_smoothConditionalMinEntropy_of_candidate_of_lt_sqrt_trace
      C.oneShotConversePurifiedRadius_nonneg hsourceTrace hcandConverse
  have hdiscard :=
    C.converseInputARSource_smoothConditionalMinEntropy_le_log2_card_add_tensorPower
      C.oneShotConversePurifiedRadius C.oneShotConversePurifiedRadius_nonneg hradius
  have hdiscardIso :
      (C.converseInputPureVector.state.marginalA.toSubnormalized.sourceIsometryApply
        (ReferenceIsometry.ofEquiv
          (Equiv.prodComm (TensorPower a n) kA))).smoothConditionalMinEntropy
          C.oneShotConversePurifiedRadius C.oneShotConversePurifiedRadius_nonneg (by
            rw [SubnormalizedState.sourceIsometryApply_trace_re]
            exact hsourceTrace) <=
        log2 (Fintype.card kA : Real) +
          (psi.state.marginalAC.tensorPowerBipartite n).toSubnormalized.smoothConditionalMinEntropy
              C.oneShotConversePurifiedRadius
              C.oneShotConversePurifiedRadius_nonneg (by
                rw [State.toSubnormalized_trace]
                simpa using hradius) := by
    simpa only [C.converseInputARSource_eq_sourceIsometryApply] using hdiscard
  have hdiscardInput :
      C.converseInputPureVector.state.marginalA.toSubnormalized.smoothConditionalMinEntropy
            C.oneShotConversePurifiedRadius
            C.oneShotConversePurifiedRadius_nonneg hsourceTrace <=
        log2 (Fintype.card kA : Real) +
          (psi.state.marginalAC.tensorPowerBipartite n).toSubnormalized.smoothConditionalMinEntropy
              C.oneShotConversePurifiedRadius
              C.oneShotConversePurifiedRadius_nonneg (by
                rw [State.toSubnormalized_trace]
                simpa using hradius) := by
    simpa only [C.converseInputPureVector.state.marginalA.toSubnormalized
      |>.smoothConditionalMinEntropy_sourceIsometryApply
        (ReferenceIsometry.ofEquiv (Equiv.prodComm (TensorPower a n) kA))
        C.oneShotConversePurifiedRadius_nonneg hsourceTrace] using hdiscardIso
  calc
    log2 (Fintype.card lA : Real) <= h' := hlog
    _ <= C.converseInputPureVector.state.marginalA.toSubnormalized.smoothConditionalMinEntropy
          C.oneShotConversePurifiedRadius
          C.oneShotConversePurifiedRadius_nonneg hsourceTrace := hcandidateLe
    _ <= log2 (Fintype.card kA : Real) +
        psi.state.marginalAC.tensorPowerSubnormalizedSmoothConditionalMinEntropy
          C.oneShotConversePurifiedRadius n
          C.oneShotConversePurifiedRadius_nonneg hradius := by
      simpa only [State.tensorPowerSubnormalizedSmoothConditionalMinEntropy_eq]
        using hdiscardInput

/-- Fixed-radius rate form of the one-shot smooth-min-entropy converse. -/
theorem oneShotSmoothMinEntropyRate_converse
    (eta : Real) (heta1 : eta < 1)
    (hradius : C.oneShotConversePurifiedRadius <= eta) (hn : 0 < n) :
    -psi.state.marginalAC.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
        eta n (C.oneShotConversePurifiedRadius_nonneg.trans hradius) heta1 <=
      C.netEntanglementRate := by
  letI : Nonempty a := Nonempty.map (fun i ↦ i.1.1) psi.state.nonempty
  letI : Nonempty r := Nonempty.map (fun i ↦ i.2) psi.state.nonempty
  have heta0 : 0 <= eta := C.oneShotConversePurifiedRadius_nonneg.trans hradius
  have hradius1 : C.oneShotConversePurifiedRadius < 1 :=
    lt_of_le_of_lt hradius heta1
  have hone := C.oneShotSmoothMinEntropy_converse hradius1
  have hradiusTrace :
      C.oneShotConversePurifiedRadius <
        Real.sqrt
          (psi.state.marginalAC.tensorPowerBipartite n).toSubnormalized.matrix.trace.re := by
    rw [State.toSubnormalized_trace]
    simpa using hradius1
  have hetaTrace :
      eta <
        Real.sqrt
          (psi.state.marginalAC.tensorPowerBipartite n).toSubnormalized.matrix.trace.re := by
    rw [State.toSubnormalized_trace]
    simpa using heta1
  have hmonoRaw :=
    (psi.state.marginalAC.tensorPowerBipartite n).toSubnormalized
      |>.smoothConditionalMinEntropy_mono
        C.oneShotConversePurifiedRadius_nonneg heta0 hradius hradiusTrace hetaTrace
  have hmono :
      psi.state.marginalAC.tensorPowerSubnormalizedSmoothConditionalMinEntropy
          C.oneShotConversePurifiedRadius n
            C.oneShotConversePurifiedRadius_nonneg hradius1 <=
        psi.state.marginalAC.tensorPowerSubnormalizedSmoothConditionalMinEntropy
          eta n heta0 heta1 := by
    simpa only [State.tensorPowerSubnormalizedSmoothConditionalMinEntropy_eq] using hmonoRaw
  have hcost :
      -psi.state.marginalAC.tensorPowerSubnormalizedSmoothConditionalMinEntropy
          eta n heta0 heta1 <=
        log2 (Fintype.card kA : Real) - log2 (Fintype.card lA : Real) := by
    linarith
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  have hnR : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  have hscaled :=
    mul_le_mul_of_nonneg_left hcost (le_of_lt (one_div_pos.mpr hnR))
  rw [State.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate_eq,
    netEntanglementRate, if_neg hn_ne]
  calc
    -(1 / (n : Real) *
        psi.state.marginalAC.tensorPowerSubnormalizedSmoothConditionalMinEntropy
          eta n heta0 heta1) =
        (1 / (n : Real)) *
          (-psi.state.marginalAC.tensorPowerSubnormalizedSmoothConditionalMinEntropy
            eta n heta0 heta1) := by ring
    _ <= (1 / (n : Real)) *
        (log2 (Fintype.card kA : Real) - log2 (Fintype.card lA : Real)) :=
      hscaled
    _ = (log2 (Fintype.card kA : Real) - log2 (Fintype.card lA : Real)) /
        (n : Real) := by ring

end StateMergingBlockProtocol

end

end QIT
