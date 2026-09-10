/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Coding.EntanglementAssisted.Basic
public import QuantumLib.QIT.Util.TensorPower
public import QuantumLib.QIT.Information.CQChannel
public import QuantumLib.QIT.HypothesisTesting.ComparatorTest
public import QuantumLib.QIT.HypothesisTesting.DPI

/-!
# One-shot entanglement-assisted converse interface

This module contains the protocol-state infrastructure for the one-shot
entanglement-assisted meta-converse of
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:327-394].

The source proof first forms the uniform classical message register, applies
the decoder to the channel output and Bob side-information register, and then
uses the equality-comparator test.  The channel-optimization step is provided
by `QIT.HypothesisTesting.DPI`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

universe u v w x y

namespace QIT

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace EntanglementAssistedClassicalCode

variable {N : CPTPMap a b} {n : ℕ}
variable {M : Type w} [Fintype M] [DecidableEq M] [Nonempty M]
variable {EA : Type x} [Fintype EA] [DecidableEq EA]
variable {EB : Type y} [Fintype EB] [DecidableEq EB]

/-- Uniform message ensemble of Bob's pre-decoding output states. -/
def uniformOutputEnsemble (C : EntanglementAssistedClassicalCode N n M EA EB) :
    MEnsemble (TensorPower b n × EB) M :=
  .ofProbs (uniformMessageProb (M := M)) (uniformMessageProb_sum (M := M)) C.outputState

/-- Uniform message ensemble of Alice's channel-input and Bob side-information
states before the communication channel acts. -/
def uniformInputEnsemble (C : EntanglementAssistedClassicalCode N n M EA EB) :
    MEnsemble (TensorPower a n × EB) M :=
  .ofProbs (uniformMessageProb (M := M)) (uniformMessageProb_sum (M := M)) C.channelInputState

/-- Cq state whose classical register is the uniform transmitted message and
whose quantum register is Bob's pre-decoding state for that message. -/
def preDecodedMessageOutputState
    (C : EntanglementAssistedClassicalCode N n M EA EB) :
    MState (M × (TensorPower b n × EB)) :=
  C.uniformOutputEnsemble.cqState

/-- Cq state whose classical register is the uniform transmitted message and
whose quantum register is the encoded channel input together with Bob's retained
side-information. -/
def preDecodedMessageInputState
    (C : EntanglementAssistedClassicalCode N n M EA EB) :
    MState (M × (TensorPower a n × EB)) :=
  C.uniformInputEnsemble.cqState

/-- The pre-decoding message/output cq state is obtained from the corresponding
message/input cq state by applying the memoryless channel to the input block and
leaving Bob's side-information untouched. -/
theorem preDecodedMessageOutputState_eq_channel_preDecodedMessageInputState
    (C : EntanglementAssistedClassicalCode N n M EA EB) :
    C.preDecodedMessageOutputState =
      ((CPTPOp.id (dIn := M)).prod ((N.tensorPower n).prod (CPTPOp.id (dIn := EB))))
        C.preDecodedMessageInputState := by
  apply MState.ext
  change C.uniformOutputEnsemble.cqState.m =
    (((CPTPOp.id (dIn := M)).prod ((N.tensorPower n).prod (CPTPOp.id (dIn := EB))))
      C.uniformInputEnsemble.cqState).m
  rw [applyState_id_prod_cqState_matrix C.uniformInputEnsemble
    ((N.tensorPower n).prod (CPTPOp.id (dIn := EB)))]
  rw [MEnsemble.cqState_matrix]
  refine Finset.sum_congr rfl ?_
  intro m _
  change
    ((uniformMessageProb (M := M) m : ℂ) •
      Matrix.kronecker (Matrix.single m m (1 : ℂ)) (C.outputState m).m) =
    ((uniformMessageProb (M := M) m : ℂ) •
      Matrix.kronecker (Matrix.single m m (1 : ℂ))
        (((N.tensorPower n).prod (CPTPOp.id (dIn := EB)))
          (C.channelInputState m)).m)
  rfl

/-- For one channel use, repartition `M × (A¹ × E_B)` as `(M × E_B) × A`,
dropping the terminal unit tensor-power register. -/
def oneUseMessageSideInfoChannelEquiv
    (M q EB : Type*) : (M × (TensorPower q 1 × EB)) ≃ ((M × EB) × q) where
  toFun x := ((x.1, x.2.2), x.2.1.1)
  invFun y := (y.1.1, ((y.2, PUnit.unit), y.1.2))
  left_inv x := by
    rcases x with ⟨m, ⟨⟨q, u⟩, eb⟩⟩
    cases u
    rfl
  right_inv y := by
    rcases y with ⟨⟨m, eb⟩, q⟩
    rfl

/-- For one channel use, drop the terminal unit tensor-power register in the
right side of a message/output cq state. -/
def oneUseMessageOutputEquiv
    (M q EB : Type*) : (M × (TensorPower q 1 × EB)) ≃ (M × (q × EB)) :=
  Equiv.prodCongr (Equiv.refl M) (Equiv.prodCongr (tensorPowerOneEquiv q) (Equiv.refl EB))

/-- One-use pre-channel state with the message and Bob side-information grouped
as the reference register and the channel input as the target register. -/
def oneUseReferenceInputState
    (C : EntanglementAssistedClassicalCode N 1 M EA EB) :
    MState ((M × EB) × a) :=
  C.preDecodedMessageInputState.reindex (oneUseMessageSideInfoChannelEquiv M a EB)

/-- One-use pre-decoding output state with the message and Bob side-information
grouped as the reference register and the channel output as the target register. -/
def oneUseReferenceOutputState
    (C : EntanglementAssistedClassicalCode N 1 M EA EB) :
    MState ((M × EB) × b) :=
  C.preDecodedMessageOutputState.reindex (oneUseMessageSideInfoChannelEquiv M b EB)

/-- In one channel use, the reference-grouped pre-decoding state is exactly the
output of `N` acting on the reference-grouped encoded input state. -/
theorem oneUseReferenceOutputState_eq_channel_referenceInputState
    (C : EntanglementAssistedClassicalCode N 1 M EA EB) :
    C.oneUseReferenceOutputState =
      ((CPTPOp.id (dIn := M × EB)).prod N) C.oneUseReferenceInputState := by
  apply MState.ext
  simp only [oneUseReferenceOutputState, MState.reindex_matrix, CPTPOp.mat_coe_eq_apply_mat,
    CPTPOp.prod_map]
  ext x y
  rcases x with ⟨⟨xm, xe⟩, xb⟩
  rcases y with ⟨⟨ym, ye⟩, yb⟩
  have h0 :=
    congrArg DensityOp.m
      (C.preDecodedMessageOutputState_eq_channel_preDecodedMessageInputState)
  rw [CPTPOp.mat_coe_eq_apply_mat] at h0
  have h := congrFun (congrFun h0 (xm, ((xb, PUnit.unit), xe))) (ym, ((yb, PUnit.unit), ye))
  change
    C.preDecodedMessageOutputState.m ((xm, ((xb, PUnit.unit), xe)) : M × (TensorPower b 1 × EB))
        (ym, ((yb, PUnit.unit), ye)) =
      MatrixMap.kron (CPTPOp.id (dIn := M × EB)).map N.map
        C.oneUseReferenceInputState.m
        ((xm, xe), xb) ((ym, ye), yb)
  rw [h, CPTPOp.prod_map,
    MatrixMap.kron_idChannel_left_apply_slice]
  change
    ((N.tensorPower 1).prod (CPTPOp.id (dIn := EB))).map
        (Matrix.of fun z z' =>
          C.preDecodedMessageInputState.m (xm, z) (ym, z'))
        ((xb, PUnit.unit), xe) ((yb, PUnit.unit), ye) =
      MatrixMap.kron (CPTPOp.id (dIn := M × EB)).map N.map
        C.oneUseReferenceInputState.m
        ((xm, xe), xb) ((ym, ye), yb)
  rw [CPTPOp.prod_map,
    MatrixMap.kron_idChannel_apply_slice]
  rw [CPTPOp.tensorPower_succ]
  change (N.prod (N.tensorPower 0)).map _ _ _ = _
  simp only [CPTPOp.prod_map, CPTPOp.tensorPower_zero_map]
  refine Eq.trans (MatrixMap.kron_unit_apply_slice N.map _ _ _) ?_
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  simp only [oneUseReferenceInputState, MState.reindex_matrix, Matrix.submatrix_apply,
    oneUseMessageSideInfoChannelEquiv, Equiv.coe_fn_symm_mk]
  rfl

/-- Alice's encoding is local to her share, so Bob's retained side-information
marginal is unchanged. -/
theorem channelInputState_traceLeft
    (C : EntanglementAssistedClassicalCode N n M EA EB) (m : M) :
    (C.channelInputState m).traceLeft = C.sharedState.traceLeft := by
  unfold channelInputState
  exact MState.traceLeft_applyState_prod_id C.sharedState (C.encoder m)

/-- The transmitted-message marginal of the pre-channel cq state is uniform. -/
theorem preDecodedMessageInputState_traceRight
    (C : EntanglementAssistedClassicalCode N n M EA EB) :
    C.preDecodedMessageInputState.traceRight = uniformMessageState (M := M) := by
  apply MState.ext
  rw [MState.traceRight_m]
  change Matrix.traceRight
      C.uniformInputEnsemble.cqState.m =
    (uniformMessageState (M := M)).m
  rw [Classical.traceRight_cqState_eq_diagonalState]
  rfl

/-- For one use, after grouping message and Bob side-information together as
the reference register, the input reference marginal is the product
`π_M ⊗ ρ_{E_B}`. -/
theorem oneUseReferenceInputState_traceRight
    (C : EntanglementAssistedClassicalCode N 1 M EA EB) :
    C.oneUseReferenceInputState.traceRight =
      (uniformMessageState (M := M)).prod C.sharedState.traceLeft := by
  apply MState.ext
  simp only [oneUseReferenceInputState, MState.traceRight_m, MState.reindex_matrix]
  ext x y
  rcases x with ⟨xm, xe⟩
  rcases y with ⟨ym, ye⟩
  by_cases hm : xm = ym
  · subst ym
    change
      (∑ z : a,
        C.preDecodedMessageInputState.m
            ((xm, ((z, PUnit.unit), xe)) : M × (TensorPower a 1 × EB))
          (xm, ((z, PUnit.unit), ye))) =
      ((uniformMessageState (M := M)).prod C.sharedState.traceLeft).m (xm, xe) (xm, ye)
    have hblock :
        ∀ z : a,
          C.preDecodedMessageInputState.m
                ((xm, ((z, PUnit.unit), xe)) : M × (TensorPower a 1 × EB))
              (xm, ((z, PUnit.unit), ye)) =
            uniformMessageProb (M := M) xm •
              (C.channelInputState xm).m (((z, PUnit.unit), xe) : TensorPower a 1 × EB)
                ((z, PUnit.unit), ye) := by
      intro z
      show C.uniformInputEnsemble.cqState.m _ _ = _
      simp only [uniformInputEnsemble, MEnsemble.cqState_matrix, Matrix.sum_apply,
        Matrix.smul_apply]
      rw [Finset.sum_eq_single xm]
      · simp [Matrix.kronecker]
      · intro m _ hm
        simp [Matrix.kronecker, hm]
      · simp
    simp_rw [hblock]
    rw [← Finset.smul_sum]
    have hmarg :=
      congrFun
        (congrFun
          (congrArg DensityOp.m (C.channelInputState_traceLeft xm)) xe) ye
    have hmarg' :
        (∑ z : a,
          (C.channelInputState xm).m (((z, PUnit.unit), xe) : TensorPower a 1 × EB)
            ((z, PUnit.unit), ye)) =
            C.sharedState.traceLeft.m xe ye := by
      have hmargTensor :
          (∑ i : TensorPower a 1,
            (C.channelInputState xm).m (i, xe) (i, ye)) =
              C.sharedState.traceLeft.m xe ye := by
        simpa [MState.traceLeft_m, Matrix.traceLeft] using hmarg
      have hsumTensor :
          (∑ i : TensorPower a 1,
            (C.channelInputState xm).m (i, xe) (i, ye)) =
          ∑ z : a,
            (C.channelInputState xm).m (((z, PUnit.unit), xe) : TensorPower a 1 × EB)
              ((z, PUnit.unit), ye) := by
        exact Fintype.sum_equiv (tensorPowerOneEquiv a)
          (fun i : TensorPower a 1 => (C.channelInputState xm).m (i, xe) (i, ye))
          (fun z : a => (C.channelInputState xm).m (((z, PUnit.unit), xe) : TensorPower a 1 × EB)
            ((z, PUnit.unit), ye))
          (by
            intro i
            rcases i with ⟨z, u⟩
            cases u
            rfl)
      exact hsumTensor.symm.trans hmargTensor
    change
      uniformMessageProb (M := M) xm •
          (∑ z : a,
            (C.channelInputState xm).m (((z, PUnit.unit), xe) : TensorPower a 1 × EB)
              ((z, PUnit.unit), ye)) =
        ((uniformMessageState (M := M)).prod C.sharedState.traceLeft).m
          (xm, xe) (xm, ye)
    rw [hmarg']
    simp [Matrix.traceLeft,
      uniformMessageState, Classical.diagonalState_matrix, uniformMessageProb, Algebra.smul_def]
  · change
      (∑ z : a,
        C.preDecodedMessageInputState.m
            ((xm, ((z, PUnit.unit), xe)) : M × (TensorPower a 1 × EB))
          (ym, ((z, PUnit.unit), ye))) =
      ((uniformMessageState (M := M)).prod C.sharedState.traceLeft).m (xm, xe) (ym, ye)
    have hblock :
        ∀ z : a,
          C.preDecodedMessageInputState.m
                ((xm, ((z, PUnit.unit), xe)) : M × (TensorPower a 1 × EB))
              (ym, ((z, PUnit.unit), ye)) = 0 := by
      intro z
      show C.uniformInputEnsemble.cqState.m _ _ = _
      simp only [uniformInputEnsemble, MEnsemble.cqState_matrix, Matrix.sum_apply,
        Matrix.smul_apply]
      rw [Finset.sum_eq_zero]
      intro m _
      by_cases hmx : m = xm
      · subst m
        simp [Matrix.kronecker, hm]
      · simp [Matrix.kronecker, hmx]
    simp [hblock, uniformMessageState, Classical.diagonalState_matrix, hm]

/-- For one use, the output reference marginal is the same product
`π_M ⊗ ρ_{E_B}` because the physical channel acts only on the output register. -/
theorem oneUseReferenceOutputState_traceRight
    (C : EntanglementAssistedClassicalCode N 1 M EA EB) :
    C.oneUseReferenceOutputState.traceRight =
      (uniformMessageState (M := M)).prod C.sharedState.traceLeft := by
  rw [C.oneUseReferenceOutputState_eq_channel_referenceInputState]
  rw [MState.traceRight_applyState_id_prod]
  exact C.oneUseReferenceInputState_traceRight

/-- The one-use reference marginal of the pre-decoding output state factors as
the product of its message and Bob-side-information marginals. -/
theorem oneUseReferenceOutputState_traceRight_eq_prod_marginals
    (C : EntanglementAssistedClassicalCode N 1 M EA EB) :
    C.oneUseReferenceOutputState.traceRight =
      C.oneUseReferenceOutputState.traceRight.traceRight.prod
        C.oneUseReferenceOutputState.traceRight.traceLeft := by
  rw [C.oneUseReferenceOutputState_traceRight]
  have hA :
      (((uniformMessageState (M := M)).prod C.sharedState.traceLeft).traceRight =
        uniformMessageState (M := M)) := by
    apply MState.ext
    rw [MState.traceRight_m]
    exact MState.traceRight_prod (uniformMessageState (M := M)) C.sharedState.traceLeft
  have hB :
      (((uniformMessageState (M := M)).prod C.sharedState.traceLeft).traceLeft =
        C.sharedState.traceLeft) := by
    apply MState.ext
    rw [MState.traceLeft_m]
    exact MState.traceLeft_prod (uniformMessageState (M := M)) C.sharedState.traceLeft
  rw [hA, hB]

/-- Dropping the terminal unit tensor-power register identifies the usual
message/output cq state with the source proof's repartitioned
`(M E_B) : B` state. -/
theorem preDecodedMessageOutputState_reindex_oneUseMessageOutputEquiv
    (C : EntanglementAssistedClassicalCode N 1 M EA EB) :
    C.preDecodedMessageOutputState.reindex (oneUseMessageOutputEquiv M b EB) =
      C.oneUseReferenceOutputState.reindex (MState.messageOutputSideInfoEquiv M EB b) := by
  apply MState.ext
  simp only [oneUseReferenceOutputState, MState.reindex_matrix]
  ext x y
  rcases x with ⟨xm, xb, xe⟩
  rcases y with ⟨ym, yb, ye⟩
  rfl

set_option maxRecDepth 4000 in
/-- One-use pre-decoding message/output states are bounded by the channel
optimized extended-real hypothesis-testing mutual information.

This is the channel-optimization part of the one-shot converse: first regroup
Bob's retained side information with the message reference, then use the
product reference marginal `θ_{ME_B}=π_M⊗θ_{E_B}`, and finally optimize over
all mixed input-reference states of the channel. -/
theorem preDecodedMessageOutputState_hypothesisTestingMutualInformation_le_channel
    (C : EntanglementAssistedClassicalCode N 1 M EA EB)
    (ε : ℝ) (hε : 0 ≤ ε) :
    C.preDecodedMessageOutputState.hypothesisTestingMutualInformation ε ≤
      N.hypothesisTestingMutualInformation ε := by
  let dropBE : (TensorPower b 1 × EB) ≃ (b × EB) :=
    Equiv.prodCongr (tensorPowerOneEquiv b) (Equiv.refl EB)
  have hdrop :
      (C.preDecodedMessageOutputState.reindex
          (Equiv.prodCongr (Equiv.refl M) dropBE)).hypothesisTestingMutualInformation ε =
        C.preDecodedMessageOutputState.hypothesisTestingMutualInformation ε := by
    exact MState.hypothesisTestingMutualInformation_reindex_prodCongr
      C.preDecodedMessageOutputState ε hε (Equiv.refl M) dropBE
  have hstate :
      C.preDecodedMessageOutputState.reindex
          (Equiv.prodCongr (Equiv.refl M) dropBE) =
        C.oneUseReferenceOutputState.reindex (MState.messageOutputSideInfoEquiv M EB b) := by
    simpa [dropBE, oneUseMessageOutputEquiv] using
      C.preDecodedMessageOutputState_reindex_oneUseMessageOutputEquiv
  have hrepart :
      (C.oneUseReferenceOutputState.reindex
          (MState.messageOutputSideInfoEquiv M EB b)).hypothesisTestingMutualInformation ε ≤
        C.oneUseReferenceOutputState.hypothesisTestingMutualInformation ε :=
    MState.hypothesisTestingMutualInformation_repartition_le_of_traceRight_eq_prod
      C.oneUseReferenceOutputState ε hε
      C.oneUseReferenceOutputState_traceRight_eq_prod_marginals
  have hchan :
      C.oneUseReferenceOutputState.hypothesisTestingMutualInformation ε ≤
        N.hypothesisTestingMutualInformation ε := by
    rw [C.oneUseReferenceOutputState_eq_channel_referenceInputState]
    exact N.mixedInputOutput_hypothesisTestingMutualInformation_le_channel
      C.oneUseReferenceInputState ε hε
  rw [← hdrop]
  rw [hstate]
  exact hrepart.trans hchan

/-- Joint state of the transmitted message and Bob's decoded message, obtained
from the classical distribution induced by the decoder POVM. -/
def uniformDecodedMessageProb
    (C : EntanglementAssistedClassicalCode N n M EA EB) :
    M × M → ℝ≥0 :=
  fun p => uniformMessageProb (M := M) p.1 * C.decoder.prob (C.outputState p.1) p.2

/-- The transmitted/decoded-message joint probabilities sum to one. -/
theorem uniformDecodedMessageProb_sum
    (C : EntanglementAssistedClassicalCode N n M EA EB) :
    ∑ p : M × M, C.uniformDecodedMessageProb p = 1 := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ m : M, ∑ mhat : M,
        uniformMessageProb (M := M) m * C.decoder.prob (C.outputState m) mhat) =
        ∑ m : M, uniformMessageProb (M := M) m *
          (∑ mhat : M, C.decoder.prob (C.outputState m) mhat) := by
          refine Finset.sum_congr rfl ?_
          intro m _
          rw [Finset.mul_sum]
    _ = ∑ m : M, uniformMessageProb (M := M) m := by
          refine Finset.sum_congr rfl ?_
          intro m _
          rw [C.decoder.sum_prob, mul_one]
    _ = 1 := uniformMessageProb_sum (M := M)

/-- Joint state of the transmitted message and Bob's decoded message. -/
def uniformDecodedMessageState
    (C : EntanglementAssistedClassicalCode N n M EA EB) :
    MState (M × M) :=
  Classical.diagonalState C.uniformDecodedMessageProb C.uniformDecodedMessageProb_sum

/-- The decoded classical message-pair state is obtained by measuring the
pre-decoding cq state with Bob's decoder on the second register. -/
theorem uniformDecodedMessageState_eq_measure_preDecoded
    (C : EntanglementAssistedClassicalCode N n M EA EB) :
    C.uniformDecodedMessageState =
      ((CPTPOp.id (dIn := M)).prod (POVM.measureDiscard C.decoder))
        C.preDecodedMessageOutputState := by
  apply MState.ext
  ext p q
  rcases p with ⟨m, mhat⟩
  rcases q with ⟨m', mhat'⟩
  change C.uniformDecodedMessageState.m (m, mhat) (m', mhat') =
    (((CPTPOp.id (dIn := M)).prod (POVM.measureDiscard C.decoder))
      C.uniformOutputEnsemble.cqState).m (m, mhat) (m', mhat')
  rw [applyState_id_prod_cqState_matrix C.uniformOutputEnsemble
    (POVM.measureDiscard C.decoder)]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  by_cases hm : m = m'
  · subst m'
    by_cases hhat : mhat = mhat'
    · subst mhat'
      have hmeas : ((C.outputState m).m * C.decoder.effects mhat).trace =
          (C.decoder.prob (C.outputState m) mhat : ℂ) := by
        rw [← Matrix.diagonal_apply_eq
            (fun y => ((C.outputState m).m * C.decoder.effects y).trace) mhat,
          ← POVM.measureDiscard_map_state_diagonal, ← CPTPOp.mat_coe_eq_apply_mat,
          ← Classical.measuredState_eq_measure_applyState]
        simp
      rw [Finset.sum_eq_single m]
      · simp [uniformDecodedMessageState, Matrix.sum_apply, Matrix.single_apply,
          uniformDecodedMessageProb, uniformOutputEnsemble, Matrix.kronecker,
          hmeas]
      · intro x _ hx
        simp [Matrix.kronecker, hx]
      · simp
    · rw [Finset.sum_eq_single m]
      · have hne : ∀ c : M, ¬(c = mhat ∧ c = mhat') := fun c hc => hhat (hc.1 ▸ hc.2)
        simp [uniformDecodedMessageState, Matrix.sum_apply,
          uniformOutputEnsemble, Matrix.kronecker, hne, hhat]
      · intro x _ hx
        simp [Matrix.kronecker, hx]
      · simp
  · rw [Finset.sum_eq_zero]
    · simp [uniformDecodedMessageState, hm]
    · intro x _
      by_cases hx : x = m
      · subst x
        simp [Matrix.kronecker, hm]
      · simp [Matrix.kronecker, hx]

/-- Measuring Bob's pre-decoding register cannot increase optimized
extended-real hypothesis-testing mutual information. -/
theorem uniformDecodedMessageState_hypothesisTestingMutualInformation_le_preDecoded
    (C : EntanglementAssistedClassicalCode N n M EA EB) (ε : ℝ) (hε : 0 ≤ ε) :
    C.uniformDecodedMessageState.hypothesisTestingMutualInformation ε ≤
      C.preDecodedMessageOutputState.hypothesisTestingMutualInformation ε := by
  rw [C.uniformDecodedMessageState_eq_measure_preDecoded]
  exact MState.hypothesisTestingMutualInformation_dataProcessing_right
    C.preDecodedMessageOutputState (POVM.measureDiscard C.decoder) ε hε

/-- The transmitted-message marginal of the pre-decoding cq state is uniform. -/
theorem preDecodedMessageOutputState_traceRight
    (C : EntanglementAssistedClassicalCode N n M EA EB) :
    C.preDecodedMessageOutputState.traceRight = uniformMessageState (M := M) := by
  apply MState.ext
  rw [MState.traceRight_m]
  change Matrix.traceRight
      C.uniformOutputEnsemble.cqState.m =
    (uniformMessageState (M := M)).m
  rw [Classical.traceRight_cqState_eq_diagonalState]
  rfl

/-- Decoding is a right-local channel, so the transmitted-message marginal of
the decoded classical pair remains uniform. -/
theorem uniformDecodedMessageState_traceRight
    (C : EntanglementAssistedClassicalCode N n M EA EB) :
    C.uniformDecodedMessageState.traceRight = uniformMessageState (M := M) := by
  apply MState.ext
  ext m m'
  by_cases h : m = m'
  · subst m'
    simp only [MState.traceRight_m, Matrix.traceRight, Matrix.of_apply, uniformDecodedMessageState,
      Classical.diagonalState_matrix, uniformDecodedMessageProb, uniformMessageState_matrix,
      Matrix.diagonal_apply_eq]
    have hsum :
        ∑ x : M, uniformMessageProb (M := M) m *
            C.decoder.prob (C.outputState m) x =
          uniformMessageProb (M := M) m := by
      rw [← Finset.mul_sum, C.decoder.sum_prob, mul_one]
    exact_mod_cast hsum
  · simp [Matrix.traceRight, uniformDecodedMessageState,
      Classical.diagonalState, uniformDecodedMessageProb, uniformMessageState, h]

/-- The equality-comparator accept probability is the uniform average decoding
success probability. -/
theorem uniformDecodedMessageState_comparator_accept
    (C : EntanglementAssistedClassicalCode N n M EA EB) :
    effectAcceptProbability C.uniformDecodedMessageState (comparatorEffect (M := M)) =
      ∑ m : M, (uniformMessageProb (M := M) m : ℝ) * C.successProbability m := by
  unfold effectAcceptProbability EntanglementAssistedClassicalCode.successProbability
  calc
    (∑ p : M × M,
        (∑ q : M × M,
          C.uniformDecodedMessageState.m p q * comparatorEffect (M := M) q p)).re =
        (∑ p : M × M,
          C.uniformDecodedMessageState.m p p *
            comparatorEffect (M := M) p p).re := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro p _
          exact Finset.sum_eq_single_of_mem p (Finset.mem_univ p) (by
            intro q _ hq
            have hzero : comparatorEffect (M := M) q p = 0 := by
              unfold comparatorEffect
              exact Matrix.diagonal_apply_ne _ hq
            rw [hzero, mul_zero])
    _ = (∑ p : M × M,
          (if p.1 = p.2 then
            (uniformMessageProb (M := M) p.1 : ℂ) *
              (C.decoder.prob (C.outputState p.1) p.2 : ℂ)
          else 0)).re := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro p _
          by_cases h : p.1 = p.2
          · simp [uniformDecodedMessageState, Classical.diagonalState,
              uniformDecodedMessageProb, comparatorEffect, h]
          · simp [uniformDecodedMessageState, Classical.diagonalState,
              uniformDecodedMessageProb, comparatorEffect, h]
    _ = (∑ m : M,
          (uniformMessageProb (M := M) m : ℂ) *
            (C.decoder.prob (C.outputState m) m : ℂ)).re := by
          congr 1
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl ?_
          intro m _
          simp
    _ = ∑ m : M, (uniformMessageProb (M := M) m : ℝ) *
          C.successProbability m := by
          simp [EntanglementAssistedClassicalCode.successProbability]

/-- Maximal-error reliability implies that the comparator test accepts the
transmitted/decoded-message pair with probability at least `1 - ε`. -/
theorem comparator_accept_ge_of_maxErrorAtMost
    (C : EntanglementAssistedClassicalCode N n M EA EB) {ε : ℝ}
    (hC : C.maxErrorAtMost ε) :
    1 - ε ≤
      effectAcceptProbability C.uniformDecodedMessageState (comparatorEffect (M := M)) := by
  rw [C.uniformDecodedMessageState_comparator_accept]
  have hsumReal :
      ∑ m : M, (uniformMessageProb (M := M) m : ℝ) = 1 := by
    exact_mod_cast (uniformMessageProb_sum (M := M))
  calc
    1 - ε = (∑ m : M, (uniformMessageProb (M := M) m : ℝ)) * (1 - ε) := by
      rw [hsumReal, one_mul]
    _ = ∑ m : M, (uniformMessageProb (M := M) m : ℝ) * (1 - ε) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ m : M, (uniformMessageProb (M := M) m : ℝ) * C.successProbability m := by
      refine Finset.sum_le_sum ?_
      intro m _
      have hsucc : 1 - ε ≤ C.successProbability m := by
        have hm := hC m
        unfold EntanglementAssistedClassicalCode.error at hm
        linarith
      exact mul_le_mul_of_nonneg_left hsucc (NNReal.coe_nonneg _)

/-- Comparator-test meta-bound for the decoded classical message pair. -/
theorem log_card_le_uniformDecodedMessageState_hypothesisTestingMutualInformation
    (C : EntanglementAssistedClassicalCode N n M EA EB) {ε : ℝ}
    (hC : C.maxErrorAtMost ε) :
    (log2 (Fintype.card M : ℝ) : EReal) ≤
      C.uniformDecodedMessageState.hypothesisTestingMutualInformation ε := by
  exact comparator_hypothesisTestingMutualInformation_lower_bound
    C.uniformDecodedMessageState ε
    C.uniformDecodedMessageState_traceRight
    (C.comparator_accept_ge_of_maxErrorAtMost hC)

/-- Reliable decoding and decoder data processing give the pre-decoding
meta-converse bound `log₂ |M| ≤ I_H^ε(M;BⁿE_B)`. -/
theorem log_card_le_preDecodedMessageOutputState_hypothesisTestingMutualInformation
    (C : EntanglementAssistedClassicalCode N n M EA EB) {ε : ℝ}
    (hε : 0 ≤ ε) (hC : C.maxErrorAtMost ε) :
    (log2 (Fintype.card M : ℝ) : EReal) ≤
      C.preDecodedMessageOutputState.hypothesisTestingMutualInformation ε :=
  (C.log_card_le_uniformDecodedMessageState_hypothesisTestingMutualInformation hC).trans
    (C.uniformDecodedMessageState_hypothesisTestingMutualInformation_le_preDecoded ε hε)

/-- One-shot entanglement-assisted hypothesis-testing meta-converse for a
fixed one-use code. -/
theorem log_card_le_channel_hypothesisTestingMutualInformation
    (C : EntanglementAssistedClassicalCode N 1 M EA EB) {ε : ℝ}
    (hε : 0 ≤ ε) (hC : C.maxErrorAtMost ε) :
    (log2 (Fintype.card M : ℝ) : EReal) ≤
      N.hypothesisTestingMutualInformation ε :=
  (C.log_card_le_preDecodedMessageOutputState_hypothesisTestingMutualInformation hε hC).trans
    (C.preDecodedMessageOutputState_hypothesisTestingMutualInformation_le_channel ε hε)

end EntanglementAssistedClassicalCode

end
end QIT

noncomputable section

namespace CPTPOp

open QIT

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

variable (N : CPTPMap a b)

/-- The one-shot hypothesis-testing mutual information is an extended-real
upper bound on every `ε`-reliable one-use entanglement-assisted classical code. -/
theorem hypothesisTestingMutualInformation_isOneShotEntanglementAssistedClassicalCapacityUpperBoundE
    {ε : ℝ} (hε : 0 ≤ ε) :
    N.IsOneShotEntanglementAssistedClassicalCapacityUpperBoundE ε
      (N.hypothesisTestingMutualInformation ε) := by
  intro M _hM _hMeq _hMne EA _hEA _hEAeq EB _hEB _hEBeq C hC
  rw [EntanglementAssistedClassicalCode.rate_one C]
  exact C.log_card_le_channel_hypothesisTestingMutualInformation hε hC

/-- One-shot entanglement-assisted hypothesis-testing converse in capacity
form, in the extended-real convention. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_le_hypothesisTestingMutualInformation
    {ε : ℝ} (hε : 0 ≤ ε) :
    N.oneShotEntanglementAssistedClassicalCapacityE ε ≤
      N.hypothesisTestingMutualInformation ε :=
  N.oneShotEntanglementAssistedClassicalCapacityE_le_of_upperBound
    (N.hypothesisTestingMutualInformation_isOneShotEntanglementAssistedClassicalCapacityUpperBoundE
      hε)

end CPTPOp

end
