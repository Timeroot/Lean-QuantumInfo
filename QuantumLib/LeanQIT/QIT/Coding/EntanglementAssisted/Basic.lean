/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy.Entropy
public import QIT.HypothesisTesting.MutualInformation
public import QIT.Core.Channel
public import QIT.Core.POVMProbability
public import QIT.Core.Pure
public import QIT.Channels.Topology

/-!
# Entanglement-assisted classical capacity API

This module records the finite-dimensional API for entanglement-assisted
classical communication.  It defines the channel mutual-information objective
`I(N)` from the BSST theorem and an operational entanglement-assisted code
surface.

The full BSST equality `C_E(N) = I(N)`, its one-shot converse/achievability
ingredients, and the final capacity-supremum squeeze are separate proof
obligations.  This file uses supremum-style definitions for `I(N)` and the
one-shot capacity, and proves separately that this finite pure-state supremum
is attained on nonempty input systems.

Source alignment:
* [KhatriWilde2024Principles, Chapters/entropies.tex:8132-8144] defines the
  channel mutual information `I(N)` as a supremum over pure input-reference
  states.
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:18-207] defines
  one-shot entanglement-assisted protocols, maximal error, and
  `C_EA^ε(N)`.
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:530-665] proves the
  hypothesis-testing one-shot lower bound by position-based coding and
  sequential decoding.
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:679-721] derives the
  Renyi one-shot lower bound.
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:857-884] states the
  capacity theorem and its one-shot proof ingredients.
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:894-982] derives
  asymptotic achievability from the one-shot bounds.
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:990-1331] derives the
  strong-converse side from the one-shot upper bounds.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
open Matrix
open Filter

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace PureVector

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- A canonical basis pure vector on a nonempty finite system. -/
def basisPureVector [Nonempty a] : PureVector a where
  amp := fun i => if i = Classical.choice (inferInstance : Nonempty a) then 1 else 0
  trace_rankOne_eq_one := by
    rw [rankOneMatrix_trace, dotProduct]
    simp

end PureVector

theorem mutualInformation_continuous :
    Continuous (fun ρ : State (Prod a b) => mutualInformation ρ) := by
  unfold mutualInformation
  exact ((State.vonNeumann_continuous.comp State.marginalA_continuous).add
    (State.vonNeumann_continuous.comp State.marginalB_continuous)).sub
    State.vonNeumann_continuous

namespace Channel

variable (N : Channel a b)

/-- Output state `(id_R ⊗ N)(|ψ⟩⟨ψ|)` for a pure input-reference state. -/
def entanglementAssistedOutputState {r : Type w} [Fintype r] [DecidableEq r]
    (ψ : PureVector (Prod r a)) : State (Prod r b) :=
  ((Channel.idChannel r).prod N).applyState ψ.state

theorem entanglementAssistedOutputState_continuous {r : Type w} [Fintype r] [DecidableEq r] :
    Continuous (fun ψ : PureVector (Prod r a) => N.entanglementAssistedOutputState ψ) :=
  (((Channel.idChannel r).prod N).applyState_continuous).comp PureVector.state_continuous

/-- Mutual information of the entanglement-assisted channel output state. -/
def entanglementAssistedMutualInformation {r : Type w} [Fintype r] [DecidableEq r]
    (ψ : PureVector (Prod r a)) : ℝ :=
  mutualInformation (N.entanglementAssistedOutputState ψ)

theorem entanglementAssistedMutualInformation_continuous
    {r : Type w} [Fintype r] [DecidableEq r] :
    Continuous (fun ψ : PureVector (Prod r a) =>
      N.entanglementAssistedMutualInformation ψ) :=
  mutualInformation_continuous.comp N.entanglementAssistedOutputState_continuous

/-- Single-letter entanglement-assisted channel information `I(N)`.

The source states `I(N)` as a maximum over pure `A A'` inputs.  The Lean API
uses `sSup` over pure states on a reference copy of the input system; the
separate compactness/maximizer proof for the attained `max` is tracked
downstream. -/
def entanglementAssistedInformation : ℝ :=
  sSup (Set.range fun ψ : PureVector (Prod a a) =>
    N.entanglementAssistedMutualInformation ψ)

/-- The supremum in `Channel.entanglementAssistedInformation` is attained on a
pure input-reference state for nonempty finite input systems. -/
theorem exists_entanglementAssistedInformation_maximizer [Nonempty a] :
    ∃ ψ : PureVector (Prod a a),
      N.entanglementAssistedInformation =
        N.entanglementAssistedMutualInformation ψ := by
  let f : PureVector (Prod a a) → ℝ :=
    fun ψ => N.entanglementAssistedMutualInformation ψ
  haveI : Nonempty (PureVector (Prod a a)) :=
    ⟨PureVector.basisPureVector⟩
  have hne : (Set.univ : Set (PureVector (Prod a a))).Nonempty :=
    Set.univ_nonempty
  obtain ⟨ψ, _hψmem, hψmax⟩ :=
    isCompact_univ.exists_isMaxOn hne
      (N.entanglementAssistedMutualInformation_continuous (r := a)).continuousOn
  refine ⟨ψ, ?_⟩
  change sSup (Set.range f) = f ψ
  refine le_antisymm ?_ ?_
  · exact csSup_le (Set.range_nonempty f) fun y hy => by
      rcases hy with ⟨φ, rfl⟩
      exact hψmax trivial
  · exact le_csSup (by
      refine ⟨f ψ, ?_⟩
      intro y hy
      rcases hy with ⟨φ, rfl⟩
      exact hψmax trivial) ⟨ψ, rfl⟩

/-- Every input-reference mutual information value is bounded by the channel
supremum `I(N)`. -/
theorem entanglementAssistedMutualInformation_le_information [Nonempty a]
    (ψ : PureVector (Prod a a)) :
    N.entanglementAssistedMutualInformation ψ ≤
      N.entanglementAssistedInformation := by
  let f : PureVector (Prod a a) → ℝ :=
    fun ψ => N.entanglementAssistedMutualInformation ψ
  haveI : Nonempty (PureVector (Prod a a)) :=
    ⟨PureVector.basisPureVector⟩
  have hne : (Set.univ : Set (PureVector (Prod a a))).Nonempty :=
    Set.univ_nonempty
  obtain ⟨ψmax, _hψmem, hψmax⟩ :=
    isCompact_univ.exists_isMaxOn hne
      (N.entanglementAssistedMutualInformation_continuous (r := a)).continuousOn
  rw [entanglementAssistedInformation]
  refine le_csSup ?_ ⟨ψ, rfl⟩
  refine ⟨f ψmax, ?_⟩
  intro y hy
  rcases hy with ⟨φ, rfl⟩
  exact hψmax trivial

end Channel

/-- Register rate for an entanglement-assisted classical message code. -/
def entanglementAssistedMessageRate (M : Type w) [Fintype M] (n : ℕ) : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card M : ℝ) / (n : ℝ)

/-- A finite entanglement-assisted classical communication code for `n` uses
of channel `N`.

Alice and Bob share a finite state on `EA × EB`.  For each message, Alice
applies an encoder channel to her share `EA` to prepare the channel input
`A^n`; Bob decodes from the channel output `B^n` together with his retained
share `EB`. -/
structure EntanglementAssistedClassicalCode (N : Channel a b) (n : ℕ)
    (M : Type w) [Fintype M] [DecidableEq M] [Nonempty M]
    (EA : Type x) [Fintype EA] [DecidableEq EA]
    (EB : Type y) [Fintype EB] [DecidableEq EB] where
  sharedState : State (Prod EA EB)
  encoder : M → Channel EA (TensorPower a n)
  decoder : POVM M (Prod (TensorPower b n) EB)

namespace EntanglementAssistedClassicalCode

variable {N : Channel a b} {n : ℕ}
variable {M : Type w} [Fintype M] [DecidableEq M] [Nonempty M]
variable {EA : Type x} [Fintype EA] [DecidableEq EA]
variable {EB : Type y} [Fintype EB] [DecidableEq EB]

/-- Joint channel-input and Bob-side state after Alice encodes a message. -/
def channelInputState (C : EntanglementAssistedClassicalCode N n M EA EB)
    (m : M) : State (Prod (TensorPower a n) EB) :=
  ((C.encoder m).prod (Channel.idChannel EB)).applyState C.sharedState

/-- Bob's received state after the `n` channel uses and before decoding. -/
def outputState (C : EntanglementAssistedClassicalCode N n M EA EB)
    (m : M) : State (Prod (TensorPower b n) EB) :=
  ((N.tensorPower n).prod (Channel.idChannel EB)).applyState
    (C.channelInputState m)

/-- Born-rule probability that Bob decodes the transmitted message. -/
def successProbability (C : EntanglementAssistedClassicalCode N n M EA EB)
    (m : M) : ℝ :=
  (C.decoder.prob (C.outputState m) m : ℝ)

/-- Message-wise error probability. -/
def error (C : EntanglementAssistedClassicalCode N n M EA EB) (m : M) : ℝ :=
  1 - C.successProbability m

/-- Maximal message error bounded by `ε`. -/
def maxErrorAtMost (C : EntanglementAssistedClassicalCode N n M EA EB)
    (ε : ℝ) : Prop :=
  ∀ m : M, C.error m ≤ ε

/-- Classical communication rate of the message set. -/
def rate (_C : EntanglementAssistedClassicalCode N n M EA EB) : ℝ :=
  entanglementAssistedMessageRate M n

@[simp]
theorem rate_one (C : EntanglementAssistedClassicalCode N 1 M EA EB) :
    C.rate = log2 (Fintype.card M : ℝ) := by
  unfold rate entanglementAssistedMessageRate
  norm_num

end EntanglementAssistedClassicalCode

namespace Channel

variable (N : Channel a b)

/-- Operational achievability of an entanglement-assisted classical rate. -/
def IsAchievableEntanglementAssistedClassicalRate (R : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
      ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
        ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
        ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
          ∃ C : EntanglementAssistedClassicalCode N n M EA EB,
            C.rate ≥ R - δ ∧ C.maxErrorAtMost ε

/-- `B` is an upper bound on every achievable entanglement-assisted classical
rate for channel `N`. -/
def IsEntanglementAssistedClassicalRateUpperBound (B : ℝ) : Prop :=
  ∀ R : ℝ, N.IsAchievableEntanglementAssistedClassicalRate R → R ≤ B

/-- Operational strong-converse rate for entanglement-assisted classical
communication.

This is the rate-normalized Lean form of the Khatri--Wilde definition
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:724-854]: for every
positive slack `δ` and every target error threshold `ε < 1`, all sufficiently
long `ε`-reliable protocols have rate strictly below `R + δ`. -/
def IsStrongConverseEntanglementAssistedClassicalRate (R : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 ≤ ε → ε < 1 →
    ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
      ∀ (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M],
        ∀ (EA : Type u) [Fintype EA] [DecidableEq EA],
          ∀ (EB : Type u) [Fintype EB] [DecidableEq EB],
            ∀ C : EntanglementAssistedClassicalCode N n M EA EB,
              C.maxErrorAtMost ε → C.rate < R + δ

/-- Operational entanglement-assisted classical capacity as the supremum of
achievable rates.  The BSST theorem later identifies this quantity with
`N.entanglementAssistedInformation`. -/
def entanglementAssistedClassicalCapacity : ℝ :=
  sSup {R : ℝ | N.IsAchievableEntanglementAssistedClassicalRate R}

/-- Strong-converse entanglement-assisted classical capacity as the infimum of
strong-converse rates, following
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:724-854]. -/
def strongConverseEntanglementAssistedClassicalCapacity : ℝ :=
  sInf {R : ℝ | N.IsStrongConverseEntanglementAssistedClassicalRate R}

/-- Finite real helper for one-shot `ε`-error entanglement-assisted classical
capacity.

This real-valued supremum is intended only for finite-domain helper statements.
The canonical source-facing one-shot capacity on the full endpoint range
`ε ∈ [0, 1]` is `oneShotEntanglementAssistedClassicalCapacityE`, because the
endpoint `ε = 1` can be `⊤`. -/
def oneShotEntanglementAssistedClassicalCapacityFinite (ε : ℝ) : ℝ :=
  sSup {R : ℝ |
    ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
      ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
        ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
          ∃ C : EntanglementAssistedClassicalCode N 1 M EA EB,
            C.maxErrorAtMost ε ∧ R = C.rate}

/-- Extended-real one-shot `ε`-error entanglement-assisted classical capacity.

This is the canonical source-facing Lean counterpart of `C_EA^ε(N)` on
`ε ∈ [0, 1]`: the supremum of one-use code rates over entanglement-assisted
classical codes whose maximal error is at most `ε`, valued in `EReal` so the
endpoint `ε = 1` can be `⊤`.  For `n = 1`, each finite code rate unfolds to
`log2 |M|`. -/
def oneShotEntanglementAssistedClassicalCapacityE (ε : ℝ) : EReal :=
  sSup {R : EReal |
    ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
      ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
        ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
          ∃ C : EntanglementAssistedClassicalCode N 1 M EA EB,
            C.maxErrorAtMost ε ∧ R = (C.rate : EReal)}

/-- `B` upper-bounds all one-shot `ε`-reliable entanglement-assisted codes. -/
def IsOneShotEntanglementAssistedClassicalCapacityUpperBound
    (ε B : ℝ) : Prop :=
  ∀ (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M],
    ∀ (EA : Type u) [Fintype EA] [DecidableEq EA],
      ∀ (EB : Type u) [Fintype EB] [DecidableEq EB],
        ∀ C : EntanglementAssistedClassicalCode N 1 M EA EB,
          C.maxErrorAtMost ε → C.rate ≤ B

/-- `B` upper-bounds all one-shot `ε`-reliable entanglement-assisted codes in
the extended-real convention. -/
def IsOneShotEntanglementAssistedClassicalCapacityUpperBoundE
    (ε : ℝ) (B : EReal) : Prop :=
  ∀ (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M],
    ∀ (EA : Type u) [Fintype EA] [DecidableEq EA],
      ∀ (EB : Type u) [Fintype EB] [DecidableEq EB],
        ∀ C : EntanglementAssistedClassicalCode N 1 M EA EB,
          C.maxErrorAtMost ε → (C.rate : EReal) ≤ B

theorem oneShotEntanglementAssistedClassicalCapacityE_le_of_upperBound
    {ε : ℝ} {B : EReal}
    (hB : N.IsOneShotEntanglementAssistedClassicalCapacityUpperBoundE ε B) :
    N.oneShotEntanglementAssistedClassicalCapacityE ε ≤ B := by
  unfold oneShotEntanglementAssistedClassicalCapacityE
  refine sSup_le ?_
  intro R hR
  rcases hR with
    ⟨M, _hM, _hMeq, _hMne, EA, _hEA, _hEAeq, EB, _hEB, _hEBeq, C, hC, rfl⟩
  exact hB M EA EB C hC

namespace OneShotEndpoint

/-- Deterministic decoder POVM that always reports one fixed message. -/
def deterministicPOVM
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (q : Type v) [Fintype q] [DecidableEq q] : POVM M q where
  effects m :=
    if m = Classical.choice (inferInstance : Nonempty M) then
      (1 : CMatrix q)
    else
      0
  pos m := by
    by_cases hm : m = Classical.choice (inferInstance : Nonempty M)
    · simp [hm, Matrix.PosSemidef.one]
    · simp [hm, Matrix.PosSemidef.zero]
  sum_eq_one := by
    ext i j
    rw [Matrix.sum_apply]
    rw [Finset.sum_eq_single (Classical.choice (inferInstance : Nonempty M))]
    · simp
    · intro m _ hm
      simp [hm]
    · intro hmem
      exact False.elim (hmem (Finset.mem_univ _))

end OneShotEndpoint

/-- A simple one-use entanglement-assisted code for an arbitrary finite
nonempty message type.

The encoder ignores the message and prepares a fixed input state, while the
decoder is deterministic.  It is used only for the `ε = 1` endpoint: every
message error is automatically at most one. -/
def arbitraryMessageOneShotEntanglementAssistedCode
    [Nonempty a]
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M] :
    EntanglementAssistedClassicalCode N 1 M PUnit PUnit where
  sharedState := State.unit.prod State.unit
  encoder _ := by
    letI : Nonempty (QIT.TensorPower a 1) :=
      ⟨(Classical.choice (inferInstance : Nonempty a), PUnit.unit)⟩
    exact
    Channel.prepare (fun _ : PUnit =>
      (PureVector.basisPureVector : PureVector (QIT.TensorPower a 1)).state)
  decoder := OneShotEndpoint.deterministicPOVM M (Prod (QIT.TensorPower b 1) PUnit)

/-- Every arbitrary-message endpoint code has maximal error at most one. -/
theorem arbitraryMessageOneShotEntanglementAssistedCode_maxErrorAtMost_one
    [Nonempty a]
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M] :
    (N.arbitraryMessageOneShotEntanglementAssistedCode M).maxErrorAtMost 1 := by
  intro m
  unfold EntanglementAssistedClassicalCode.error
    EntanglementAssistedClassicalCode.successProbability
  have hprob_nonneg :
      0 ≤
        (((N.arbitraryMessageOneShotEntanglementAssistedCode M).decoder.prob
          ((N.arbitraryMessageOneShotEntanglementAssistedCode M).outputState m) m) : ℝ) := by
    exact NNReal.coe_nonneg _
  linarith

private theorem exists_lt_log2_nat_succ (y : ℝ) :
    ∃ n : ℕ, y < log2 ((Nat.succ n : ℕ) : ℝ) := by
  have hnat : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hnat
  have hlog : Tendsto (fun n : ℕ => log2 ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    unfold log2
    exact Tendsto.atTop_div_const (Real.log_pos one_lt_two)
      (Real.tendsto_log_atTop.comp hcast)
  obtain ⟨n, _hn, hy⟩ := exists_lt_of_tendsto_atTop hlog 0 y
  exact ⟨n, by simpa [Nat.succ_eq_add_one] using hy⟩

/-- At the endpoint `ε = 1`, the full-range extended-real one-shot
entanglement-assisted classical capacity is infinite. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_one_eq_top
    [Nonempty a] :
    N.oneShotEntanglementAssistedClassicalCapacityE 1 = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro y
  obtain ⟨n, hyn⟩ := exists_lt_log2_nat_succ y
  let M : Type u := ULift (Fin (Nat.succ n))
  let C : EntanglementAssistedClassicalCode N 1 M PUnit PUnit :=
    N.arbitraryMessageOneShotEntanglementAssistedCode M
  have hcard : Fintype.card M = Nat.succ n := by
    simp [M]
  have hrate : C.rate = log2 ((Nat.succ n : ℕ) : ℝ) := by
    rw [EntanglementAssistedClassicalCode.rate_one]
    simp [M, hcard]
  have hmem :
      ((C.rate : ℝ) : EReal) ∈
        {R : EReal |
          ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
            ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
              ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
                ∃ C : EntanglementAssistedClassicalCode N 1 M EA EB,
                  C.maxErrorAtMost 1 ∧ R = (C.rate : EReal)} := by
    exact ⟨M, inferInstance, inferInstance, inferInstance,
      PUnit, inferInstance, inferInstance,
      PUnit, inferInstance, inferInstance,
      C,
      by
        simpa [C] using
          N.arbitraryMessageOneShotEntanglementAssistedCode_maxErrorAtMost_one M,
      rfl⟩
  have hle :
      ((C.rate : ℝ) : EReal) ≤
        sSup {R : EReal |
          ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
            ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
              ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
                ∃ C : EntanglementAssistedClassicalCode N 1 M EA EB,
                  C.maxErrorAtMost 1 ∧ R = (C.rate : EReal)} :=
    le_sSup hmem
  have hyC : (y : EReal) < ((C.rate : ℝ) : EReal) := by
    rw [hrate]
    exact EReal.coe_lt_coe_iff.mpr hyn
  exact hyC.trans_le hle

end Channel

/-- Source-shaped witness for one block of the entanglement-assisted direct
coding route for a fixed pure input-reference state.

The witness packages an already-constructed code and the estimates expected
from the BSST direct proof: rate at least the output mutual information minus
`δ`, and maximal decoding error at most `ε`.  This structure is an API for
later proof leaves; this module does not prove the direct coding theorem. -/
structure EntanglementAssistedDirectCodingWitness {r : Type u}
    [Fintype r] [DecidableEq r] (N : Channel a b)
    (ψ : PureVector (Prod r a)) (n : ℕ) (δ ε : ℝ)
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (EA : Type u) [Fintype EA] [DecidableEq EA]
    (EB : Type u) [Fintype EB] [DecidableEq EB] where
  code : EntanglementAssistedClassicalCode N n M EA EB
  rate_ge : code.rate ≥ N.entanglementAssistedMutualInformation ψ - δ
  maxError_le : code.maxErrorAtMost ε

/-- Source-shaped one-shot achievability witness.

The Khatri--Wilde one-shot lower bound constructs such a witness using
position-based coding and sequential decoding.  This structure records only the
resulting code and numerical lower-bound estimate; it does not prove the
one-shot theorem. -/
structure EntanglementAssistedOneShotAchievabilityWitness (N : Channel a b)
    (ε lowerBound : ℝ)
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (EA : Type u) [Fintype EA] [DecidableEq EA]
    (EB : Type u) [Fintype EB] [DecidableEq EB] where
  code : EntanglementAssistedClassicalCode N 1 M EA EB
  maxError_le : code.maxErrorAtMost ε
  lowerBound_le_rate : lowerBound ≤ code.rate

/-- Source-consistent converse estimates for entanglement-assisted classical
communication.

The Khatri--Wilde one-shot upper bounds are stated for error thresholds
`ε ∈ [0, 1)`.  This witness family records exactly the asymptotic consequence
needed for the capacity upper-bound and strong-converse assembly: for every
slack `η > 0` and every `ε < 1`, all sufficiently long `ε`-reliable codes have
rate strictly below `N.entanglementAssistedInformation + η`.

This source-shaped interface is the one used by the sandwiched-Renyi
asymptotic upper-bound route. -/
structure EntanglementAssistedSourceConverseWitnessFamily (N : Channel a b) where
  rate_lt :
    ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 ≤ ε → ε < 1 →
      ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
        ∀ (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M],
          ∀ (EA : Type u) [Fintype EA] [DecidableEq EA],
            ∀ (EB : Type u) [Fintype EB] [DecidableEq EB],
              ∀ C : EntanglementAssistedClassicalCode N n M EA EB,
                C.maxErrorAtMost ε →
                  C.rate < N.entanglementAssistedInformation + η

namespace Channel

variable (N : Channel a b)

/-- Entanglement-assisted direct achievability from a family of BSST
direct-coding witnesses.

This is the direct-coding side of the BSST route currently formalized in
Lean.  In the modern source route, the concrete witnesses come from
Khatri--Wilde one-shot position-based coding and the asymptotic passage from
their one-shot lower bound.  The one-shot theorem itself, converse,
compactness/maximizer theorem, and final capacity equality are separate proof
obligations. -/
theorem entanglementAssisted_direct_achievable_of_directCodingWitness
    {r : Type u} [Fintype r] [DecidableEq r] (ψ : PureVector (Prod r a))
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M),
            ∃ (_ : Nonempty M),
              ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
                ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
                  Nonempty (EntanglementAssistedDirectCodingWitness N ψ n δ ε M EA EB)) :
    N.IsAchievableEntanglementAssistedClassicalRate
      (N.entanglementAssistedMutualInformation ψ) := by
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨M, hMfin, hMdec, hMnonempty,
    EA, hEAfin, hEAdec, EB, hEBfin, hEBdec, ⟨witness⟩⟩ := hN0 n hn
  letI : Fintype M := hMfin
  letI : DecidableEq M := hMdec
  letI : Nonempty M := hMnonempty
  letI : Fintype EA := hEAfin
  letI : DecidableEq EA := hEAdec
  letI : Fintype EB := hEBfin
  letI : DecidableEq EB := hEBdec
  exact ⟨M, inferInstance, inferInstance, inferInstance,
    EA, inferInstance, inferInstance, EB, inferInstance, inferInstance,
    witness.code, witness.rate_ge, witness.maxError_le⟩

/-- Source-consistent converse estimates imply the ordinary capacity upper
bound.

Only the reliable range is needed here: achievability supplies codes for the
fixed threshold `ε = 1/2`, and the source-shaped witness bounds those codes. -/
theorem entanglementAssisted_information_isUpperBound_of_sourceConverseWitness
    (hconv : EntanglementAssistedSourceConverseWitnessFamily N) :
    N.IsEntanglementAssistedClassicalRateUpperBound
      N.entanglementAssistedInformation := by
  intro R hR
  refine le_of_forall_pos_le_add ?_
  intro η hη
  have hhalf : 0 < η / 2 := half_pos hη
  have heps_pos : 0 < (1 / 2 : ℝ) := by norm_num
  have heps_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have heps_lt_one : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨Nach, hNach⟩ := hR (η / 2) hhalf (1 / 2) heps_pos
  obtain ⟨Nconv, hNconv⟩ :=
    hconv.rate_lt (η / 2) hhalf (1 / 2) heps_nonneg heps_lt_one
  let n : ℕ := max Nach Nconv
  have hnAch : n ≥ Nach := Nat.le_max_left Nach Nconv
  have hnConv : n ≥ Nconv := Nat.le_max_right Nach Nconv
  obtain ⟨M, hMfin, hMdec, hMnonempty,
    EA, hEAfin, hEAdec, EB, hEBfin, hEBdec, C, hrate_ge, herror⟩ :=
    hNach n hnAch
  letI : Fintype M := hMfin
  letI : DecidableEq M := hMdec
  letI : Nonempty M := hMnonempty
  letI : Fintype EA := hEAfin
  letI : DecidableEq EA := hEAdec
  letI : Fintype EB := hEBfin
  letI : DecidableEq EB := hEBdec
  have hrate_lt :
      C.rate < N.entanglementAssistedInformation + η / 2 :=
    hNconv n hnConv M EA EB C herror
  linarith

/-- Every strong-converse rate is an upper bound on every achievable rate.

This is the order-theoretic content behind the source inequality
`C_EA(N) ≤ Ctilde_EA(N)`: an achievable sequence with rate `R - δ/2` and a
strong-converse bound at `S + δ/2` can be compared at the same blocklength. -/
theorem achievable_le_of_strongConverseRate
    {R S : ℝ}
    (hR : N.IsAchievableEntanglementAssistedClassicalRate R)
    (hS : N.IsStrongConverseEntanglementAssistedClassicalRate S) :
    R ≤ S := by
  refine le_of_forall_pos_le_add ?_
  intro η hη
  have hhalf : 0 < η / 2 := half_pos hη
  have heps_pos : 0 < (1 / 2 : ℝ) := by norm_num
  have heps_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have heps_lt_one : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨Nach, hNach⟩ := hR (η / 2) hhalf (1 / 2) heps_pos
  obtain ⟨Nstrong, hNstrong⟩ :=
    hS (η / 2) hhalf (1 / 2) heps_nonneg heps_lt_one
  let n : ℕ := max Nach Nstrong
  have hnAch : n ≥ Nach := Nat.le_max_left Nach Nstrong
  have hnStrong : n ≥ Nstrong := Nat.le_max_right Nach Nstrong
  obtain ⟨M, hMfin, hMdec, hMnonempty,
    EA, hEAfin, hEAdec, EB, hEBfin, hEBdec, C, hrate_ge, herror⟩ :=
    hNach n hnAch
  letI : Fintype M := hMfin
  letI : DecidableEq M := hMdec
  letI : Nonempty M := hMnonempty
  letI : Fintype EA := hEAfin
  letI : DecidableEq EA := hEAdec
  letI : Fintype EB := hEBfin
  letI : DecidableEq EB := hEBdec
  have hrate_lt : C.rate < S + η / 2 :=
    hNstrong n hnStrong M EA EB C herror
  have hR_lt : R - η / 2 < S + η / 2 :=
    lt_of_le_of_lt hrate_ge hrate_lt
  linarith

/-- Source-consistent converse estimates directly give the strong-converse
rate property. -/
theorem entanglementAssisted_information_isStrongConverseRate_of_sourceConverseWitness
    (hconv : EntanglementAssistedSourceConverseWitnessFamily N) :
    N.IsStrongConverseEntanglementAssistedClassicalRate
      N.entanglementAssistedInformation := by
  intro δ hδ ε hε_nonneg hε_lt_one
  exact hconv.rate_lt δ hδ ε hε_nonneg hε_lt_one

/-- Capacity upper bound from a source-consistent converse witness. -/
theorem entanglementAssistedClassicalCapacity_le_information_of_sourceConverseWitness
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (hconv : EntanglementAssistedSourceConverseWitnessFamily N) :
    N.entanglementAssistedClassicalCapacity ≤
      N.entanglementAssistedInformation := by
  unfold entanglementAssistedClassicalCapacity
  exact csSup_le ⟨N.entanglementAssistedInformation, hach⟩
    (N.entanglementAssisted_information_isUpperBound_of_sourceConverseWitness hconv)

/-- Abstract capacity squeeze from a source-consistent converse witness. -/
theorem entanglementAssistedClassicalCapacity_eq_information_of_achievable_of_sourceConverseWitness
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (hconv : EntanglementAssistedSourceConverseWitnessFamily N) :
    N.entanglementAssistedClassicalCapacity =
      N.entanglementAssistedInformation := by
  exact le_antisymm
    (N.entanglementAssistedClassicalCapacity_le_information_of_sourceConverseWitness hach hconv)
    (by
      unfold entanglementAssistedClassicalCapacity
      exact le_csSup
        ⟨N.entanglementAssistedInformation,
          N.entanglementAssisted_information_isUpperBound_of_sourceConverseWitness hconv⟩
        hach)

/-- The operational capacity is bounded by every strong-converse rate. -/
theorem entanglementAssistedClassicalCapacity_le_of_strongConverseRate
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    {S : ℝ} (hS : N.IsStrongConverseEntanglementAssistedClassicalRate S) :
    N.entanglementAssistedClassicalCapacity ≤ S := by
  unfold entanglementAssistedClassicalCapacity
  exact csSup_le ⟨N.entanglementAssistedInformation, hach⟩
    (fun R hR => N.achievable_le_of_strongConverseRate hR hS)

/-- The usual capacity is at most the strong-converse capacity. -/
theorem entanglementAssistedClassicalCapacity_le_strongConverseCapacity
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (hsc :
      N.IsStrongConverseEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation) :
    N.entanglementAssistedClassicalCapacity ≤
      N.strongConverseEntanglementAssistedClassicalCapacity := by
  unfold strongConverseEntanglementAssistedClassicalCapacity
  exact le_csInf ⟨N.entanglementAssistedInformation, hsc⟩
    (fun S hS => N.entanglementAssistedClassicalCapacity_le_of_strongConverseRate hach hS)

/-- The strong-converse capacity is at most `I(N)` when `I(N)` is a
strong-converse rate. -/
theorem strongConverseEntanglementAssistedClassicalCapacity_le_information
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (hsc :
      N.IsStrongConverseEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation) :
    N.strongConverseEntanglementAssistedClassicalCapacity ≤
      N.entanglementAssistedInformation := by
  unfold strongConverseEntanglementAssistedClassicalCapacity
  exact csInf_le
    ⟨N.entanglementAssistedClassicalCapacity, by
      intro S hS
      exact N.entanglementAssistedClassicalCapacity_le_of_strongConverseRate hach hS⟩
    hsc

/-- Abstract strong-converse capacity squeeze from a source-consistent
converse witness. -/
theorem strongConverseEntanglementAssistedClassicalCapacity_eq_information_of_achievable_of_sourceConverseWitness
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (hconv : EntanglementAssistedSourceConverseWitnessFamily N) :
    N.strongConverseEntanglementAssistedClassicalCapacity =
      N.entanglementAssistedInformation := by
  have hsc :=
    N.entanglementAssisted_information_isStrongConverseRate_of_sourceConverseWitness hconv
  exact le_antisymm
    (N.strongConverseEntanglementAssistedClassicalCapacity_le_information hach hsc)
    (le_trans
      (by
        rw [←
          N.entanglementAssistedClassicalCapacity_eq_information_of_achievable_of_sourceConverseWitness
            hach hconv])
      (N.entanglementAssistedClassicalCapacity_le_strongConverseCapacity hach hsc))

/-- Final abstract Khatri--Wilde capacity squeeze from the source-consistent
converse witness. -/
theorem entanglementAssisted_capacity_and_strongConverseCapacity_eq_information_of_sourceConverseWitness
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (hconv : EntanglementAssistedSourceConverseWitnessFamily N) :
    N.entanglementAssistedClassicalCapacity = N.entanglementAssistedInformation ∧
      N.strongConverseEntanglementAssistedClassicalCapacity =
        N.entanglementAssistedInformation :=
  ⟨N.entanglementAssistedClassicalCapacity_eq_information_of_achievable_of_sourceConverseWitness
      hach hconv,
    N.strongConverseEntanglementAssistedClassicalCapacity_eq_information_of_achievable_of_sourceConverseWitness
      hach hconv⟩


end Channel

end

end QIT
