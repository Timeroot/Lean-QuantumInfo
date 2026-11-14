/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.OneShot.Lower.Naimark
public import QIT.Coding.EntanglementAssisted.PositionNaimarkTrace
public import QIT.Information.Entropy.Log2Lemmas

/-!
# Hypothesis-testing one-shot lower-bound assembly

This module connects the hypothesis-testing effect used in the
Khatri--Wilde one-shot entanglement-assisted lower-bound proof with the
position-based sequential-decoding trace bridge
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:530-665].

The theorem here is the source-shaped assembly step after Naimark dilation:
missed-detection and false-alarm trace identities reduce the operational
one-shot capacity lower bound to the hypothesis-testing type-I and type-II
bounds.  The canonical position-based decoder construction and the
supremum/infimum optimizer and message-size rounding step are separate proof
layers.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable {N : Channel a b}
variable {M : Type u} [Fintype M] [DecidableEq M] [Nonempty M]
variable {e : Type u} [Fintype e] [DecidableEq e]
variable {testSys : Type x} [Fintype testSys] [DecidableEq testSys]

namespace SequentialDecoding

section

omit [Fintype M] [DecidableEq M] [Nonempty M]

/--
Assembly bridge for the Khatri--Wilde hypothesis-testing lower-bound route.

Given message-indexed sequential projectors and output states, it suffices to
bound the missed-detection traces by the Naimark reject probability of a
feasible hypothesis-testing effect and the false-alarm traces by its type-II
error.  This is the source-shaped trace bridge before inserting the concrete
position-based protocol.
-/
theorem decoderError_le_epsilon_of_ht_trace_bridges
    {out : Type w} [Fintype out] [DecidableEq out]
    {seqLen : ℕ} {ε η β : ℝ}
    (A : M → ProjectionSequence out (seqLen + 1)) (ω : M → State out)
    {ρ σ : State testSys} (Λ : HypothesisTestingEffect ρ (ε - η))
    (hη_pos : 0 < η) (hη_lt : η < ε)
    (hmissBridge :
      ∀ m : M,
        effectTrace (ω m) ((A m) (Fin.last seqLen)).compl.matrix ≤
          effectTrace
            (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState ρ)
            Λ.acceptNaimarkProjection.compl.matrix)
    (hfalseBridge :
      ∀ m : M, ∀ i : Fin seqLen,
        effectTrace (ω m) ((A m) (Fin.castSucc i)).matrix ≤
          Λ.typeIIError σ)
    (hβ : Λ.typeIIError σ ≤ β)
    (hsize : (seqLen : ℝ) * β ≤ η ^ 2 / (4 * ε)) :
    ∀ m : M, sequenceError (decoderTestSequence (A m)) (ω m) ≤ ε := by
  intro m
  have hmiss :
      effectTrace (ω m) ((A m) (Fin.last seqLen)).compl.matrix ≤ ε - η := by
    exact (hmissBridge m).trans Λ.fixedNaimark_reject_le
  have hfalse :
      ∀ i : Fin seqLen, effectTrace (ω m) ((A m) (Fin.castSucc i)).matrix ≤ β := by
    intro i
    exact (hfalseBridge m i).trans hβ
  exact decoderError_le_epsilon_of_trace_bounds (A m) (ω m)
    hη_pos hη_lt hmiss hfalse hsize

/--
Canonical Naimark trace-identity specialization of the sequential-decoding
error bound.

The final/source copy is placed in the head factor and the `seqLen` earlier
comparison copies are placed in the tail.  The theorem instantiates the
Khatri--Wilde identities
`eq-eacc_one_shot_lower_bound_pf1` and
`eq-eacc_one_shot_lower_bound_pf2` after fixed-base Naimark dilation, then
feeds them into the OMW/sequential-decoding estimate.
-/
theorem decoderError_le_epsilon_of_canonical_position_trace
    {seqLen : ℕ} {ε η β : ℝ}
    {ρ σ : State testSys} (Λ : HypothesisTestingEffect ρ (ε - η))
    (hη_pos : 0 < η) (hη_lt : η < ε)
    (hβ : Λ.typeIIError σ ≤ β)
    (hsize : (seqLen : ℝ) * β ≤ η ^ 2 / (4 * ε)) :
    sequenceError
        (decoderTestSequence
          (positionTraceProjectionSequence Λ.acceptNaimarkProjection seqLen))
        (positionTraceState
          (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState ρ)
          (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState σ)
          seqLen) ≤ ε := by
  refine decoderError_le_epsilon_of_trace_bounds
    (positionTraceProjectionSequence Λ.acceptNaimarkProjection seqLen)
    (positionTraceState
      (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState ρ)
      (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState σ)
      seqLen)
    hη_pos hη_lt ?_ ?_ hsize
  · calc
      effectTrace
          (positionTraceState
            (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState ρ)
            (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState σ)
            seqLen)
          ((positionTraceProjectionSequence Λ.acceptNaimarkProjection seqLen)
            (Fin.last seqLen)).compl.matrix
          = effectTrace
              (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState ρ)
              Λ.acceptNaimarkProjection.compl.matrix := by
                exact positionTrace_missedDetection_identity
                  Λ.acceptNaimarkProjection
                  (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState ρ)
                  (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState σ)
                  seqLen
      _ ≤ ε - η := Λ.fixedNaimark_reject_le
  · intro i
    calc
      effectTrace
          (positionTraceState
            (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState ρ)
            (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState σ)
            seqLen)
          ((positionTraceProjectionSequence Λ.acceptNaimarkProjection seqLen)
            (Fin.castSucc i)).matrix
          = effectTrace
              (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState σ)
              Λ.acceptNaimarkProjection.matrix := by
                exact positionTrace_falseAlarm_identity
                  Λ.acceptNaimarkProjection
                  (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState ρ)
                  (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState σ)
                  i
      _ = Λ.typeIIError σ := Λ.effectTrace_fixedNaimark_accept_comparison σ
      _ ≤ β := hβ

end

end SequentialDecoding

namespace POVM

variable {settings : Type x} {outcomes : Type u} {system : Type w}
variable [Fintype outcomes] [DecidableEq outcomes] [Inhabited outcomes]
variable [Fintype system] [DecidableEq system]

/-- The shared-family Naimark dilation preserves real effect traces after
lifting the state by the fixed family embedding. -/
theorem effectTrace_familyNaimarkProjectiveMeasurement_eq
    (M : settings → POVM outcomes system) (ρ : State system)
    (setting : settings) (outcome : outcomes) :
    SequentialDecoding.effectTrace
        (POVM.isometryLiftState ρ
          (POVM.familyNaimarkEmbedding M)
          (POVM.familyNaimarkEmbedding_isometry M))
        ((POVM.familyNaimarkProjectiveMeasurement M setting).effects outcome) =
      SequentialDecoding.effectTrace ρ ((M setting).effects outcome) := by
  unfold SequentialDecoding.effectTrace effectAcceptProbability
  rw [POVM.isometryLiftState_matrix]
  congr 1
  calc
    ((POVM.familyNaimarkEmbedding M * ρ.matrix *
          Matrix.conjTranspose (POVM.familyNaimarkEmbedding M)) *
        (POVM.familyNaimarkProjectiveMeasurement M setting).effects outcome).trace
        =
          (ρ.matrix *
            (Matrix.conjTranspose (POVM.familyNaimarkEmbedding M) *
              (POVM.familyNaimarkProjectiveMeasurement M setting).effects outcome *
              POVM.familyNaimarkEmbedding M)).trace := by
            calc
              ((POVM.familyNaimarkEmbedding M * ρ.matrix *
                    Matrix.conjTranspose (POVM.familyNaimarkEmbedding M)) *
                  (POVM.familyNaimarkProjectiveMeasurement M setting).effects outcome).trace
                  =
                    (POVM.familyNaimarkEmbedding M * ρ.matrix *
                      (Matrix.conjTranspose (POVM.familyNaimarkEmbedding M) *
                        (POVM.familyNaimarkProjectiveMeasurement M setting).effects outcome)).trace := by
                      rw [Matrix.mul_assoc, Matrix.mul_assoc]
              _ =
                    (ρ.matrix *
                      ((Matrix.conjTranspose (POVM.familyNaimarkEmbedding M) *
                          (POVM.familyNaimarkProjectiveMeasurement M setting).effects outcome) *
                        POVM.familyNaimarkEmbedding M)).trace := by
                      rw [Matrix.trace_mul_cycle]
                      rw [Matrix.trace_mul_comm]
              _ =
                    (ρ.matrix *
                      (Matrix.conjTranspose (POVM.familyNaimarkEmbedding M) *
                        (POVM.familyNaimarkProjectiveMeasurement M setting).effects outcome *
                        POVM.familyNaimarkEmbedding M)).trace := by
                      rw [Matrix.mul_assoc]
    _ = (ρ.matrix * (M setting).effects outcome).trace := by
          rw [POVM.familyNaimark_compression_projector_eq M setting outcome]

end POVM

namespace PositionBasedCodingProtocol

/-- The physical binary POVM obtained by inserting a hypothesis-testing effect
at one retained reference coordinate and the common channel output. -/
def positionHypothesisTestingPOVM
    {ρ : State (Prod a b)} {ε : ℝ} (Λ : HypothesisTestingEffect ρ ε)
    (k : ℕ) (i : Fin k) :
    POVM Bool (Prod (TensorPower b 1) (TensorPower a k)) :=
  POVM.binaryOfEffect
    (ProjectionMatrix.commonOutputReferenceEffectAt (a := a) (b := b) Λ.effect k i)
    (ProjectionMatrix.commonOutputReferenceEffectAt_posSemidef
      (a := a) (b := b) Λ.pos k i)
    (ProjectionMatrix.commonOutputReferenceEffectAt_le_one
      (a := a) (b := b) Λ.le_one k i)

@[simp]
theorem positionHypothesisTestingPOVM_true_effect
    {ρ : State (Prod a b)} {ε : ℝ} (Λ : HypothesisTestingEffect ρ ε)
    (k : ℕ) (i : Fin k) :
    (positionHypothesisTestingPOVM (a := a) (b := b) Λ k i).effects true =
      ProjectionMatrix.commonOutputReferenceEffectAt (a := a) (b := b) Λ.effect k i :=
  rfl

/-- Accept projector in the shared-family Naimark dilation for a
position-inserted hypothesis-testing effect. -/
def positionHypothesisTestingProjection
    {ρ : State (Prod a b)} {ε : ℝ} (Λ : HypothesisTestingEffect ρ ε)
    (k : ℕ) (i : Fin k) :
    ProjectionMatrix
      (POVM.FamilyNaimarkSpace
        (positionHypothesisTestingPOVM (a := a) (b := b) Λ k)) where
  matrix :=
    (POVM.familyNaimarkProjectiveMeasurement
      (positionHypothesisTestingPOVM (a := a) (b := b) Λ k) i).effects true
  isHermitian :=
    (POVM.familyNaimarkProjectiveMeasurement
      (positionHypothesisTestingPOVM (a := a) (b := b) Λ k) i).isHermitian true
  idempotent :=
    (POVM.familyNaimarkProjectiveMeasurement
      (positionHypothesisTestingPOVM (a := a) (b := b) Λ k) i).idempotent true

@[simp]
theorem positionHypothesisTestingProjection_matrix
    {ρ : State (Prod a b)} {ε : ℝ} (Λ : HypothesisTestingEffect ρ ε)
    (k : ℕ) (i : Fin k) :
    (positionHypothesisTestingProjection (a := a) (b := b) Λ k i).matrix =
      (POVM.familyNaimarkProjectiveMeasurement
        (positionHypothesisTestingPOVM (a := a) (b := b) Λ k) i).effects true :=
  rfl

/-- The lifted family-Naimark accept trace at the transmitted position equals
the one-copy hypothesis-testing accept trace. -/
theorem canonicalIndexed_truePair_liftedAcceptTrace
    (ψ : PureVector (Prod a a))
    (messageIndex : M ≃ Fin (Fintype.card M))
    {ε : ℝ}
    (Λ : HypothesisTestingEffect (N.hypothesisTestingOutputState ψ) ε)
    (decoder :
      POVM M
        (Prod (TensorPower b 1) (TensorPower a (Fintype.card M))))
    (m : M) :
    SequentialDecoding.effectTrace
        (POVM.isometryLiftState
          (((PositionBasedCodingProtocol.canonicalIndexed (N := N)
              (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder).positionOutputState m))
          (POVM.familyNaimarkEmbedding
            (positionHypothesisTestingPOVM (a := a) (b := b) Λ (Fintype.card M)))
          (POVM.familyNaimarkEmbedding_isometry
            (positionHypothesisTestingPOVM (a := a) (b := b) Λ (Fintype.card M))))
        ((positionHypothesisTestingProjection
            (a := a) (b := b) Λ (Fintype.card M) (messageIndex m)).matrix) =
      effectAcceptProbability (N.hypothesisTestingOutputState ψ) Λ.effect := by
  rw [positionHypothesisTestingProjection_matrix]
  rw [POVM.effectTrace_familyNaimarkProjectiveMeasurement_eq]
  rw [positionHypothesisTestingPOVM_true_effect]
  rw [SequentialDecoding.effectTrace_commonOutputReferenceEffectAt]
  have hstate := canonicalIndexed_truePairOutputMarginal
    (N := N) (ψ := ψ) (messageIndex := messageIndex)
    (decoder := decoder) (m := m)
  exact (congrArg (fun τ => SequentialDecoding.effectTrace τ Λ.effect) hstate).trans rfl

/-- The lifted family-Naimark accept trace at a false position equals the
one-copy comparison type-II trace. -/
theorem canonicalIndexed_falsePair_liftedAcceptTrace
    (ψ : PureVector (Prod a a))
    (messageIndex : M ≃ Fin (Fintype.card M))
    {ε : ℝ}
    (Λ : HypothesisTestingEffect (N.hypothesisTestingOutputState ψ) ε)
    (decoder :
      POVM M
        (Prod (TensorPower b 1) (TensorPower a (Fintype.card M))))
    (m : M) (i : Fin (Fintype.card M)) (hi : i ≠ messageIndex m) :
    SequentialDecoding.effectTrace
        (POVM.isometryLiftState
          (((PositionBasedCodingProtocol.canonicalIndexed (N := N)
              (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder).positionOutputState m))
          (POVM.familyNaimarkEmbedding
            (positionHypothesisTestingPOVM (a := a) (b := b) Λ (Fintype.card M)))
          (POVM.familyNaimarkEmbedding_isometry
            (positionHypothesisTestingPOVM (a := a) (b := b) Λ (Fintype.card M))))
        ((positionHypothesisTestingProjection
            (a := a) (b := b) Λ (Fintype.card M) i).matrix) =
      Λ.typeIIError
        ((N.hypothesisTestingOutputState ψ).marginalA.prod
          (N.hypothesisTestingOutputState ψ).marginalB) := by
  rw [positionHypothesisTestingProjection_matrix]
  rw [POVM.effectTrace_familyNaimarkProjectiveMeasurement_eq]
  rw [positionHypothesisTestingPOVM_true_effect]
  rw [SequentialDecoding.effectTrace_commonOutputReferenceEffectAt]
  have hstate := canonicalIndexed_falsePairOutputMarginal_comparison
    (N := N) (ψ := ψ) (messageIndex := messageIndex)
    (decoder := decoder) (m := m) (i := i) hi
  exact (congrArg (fun τ => SequentialDecoding.effectTrace τ Λ.effect) hstate).trans rfl

/-- If a finite message set has cardinality at least `2^lowerBound`, then the
position-based one-shot code rate is at least `lowerBound`. -/
theorem lowerBound_le_rate_of_rpow_two_le_card
    (P : PositionBasedCodingProtocol N M e) {lowerBound : ℝ}
    (hcard : Real.rpow 2 lowerBound ≤ (Fintype.card M : ℝ)) :
    lowerBound ≤ P.toCode.rate := by
  rw [P.rate_eq_log_card]
  have hpow_pos : 0 < Real.rpow 2 lowerBound :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) lowerBound
  have hlog := log2_mono_of_pos hpow_pos hcard
  rwa [log2_rpow_two] at hlog

/-- `2^{-log₂ x}` is the reciprocal of `x` for positive `x`. -/
private theorem rpow_two_neg_log2 {x : ℝ} (hx : 0 < x) :
    Real.rpow 2 (-log2 x) = x⁻¹ := by
  calc
    Real.rpow 2 (-log2 x) = (Real.rpow 2 (log2 x))⁻¹ := by
      exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (log2 x)
    _ = x⁻¹ := by rw [rpow_two_log2_pos hx]

/-- The real expression appearing in Khatri--Wilde's message-size choice. -/
private theorem rpow_two_ht_message_budget
    {ε η β : ℝ} (hε : 0 < ε) (hη : 0 < η) (hβ : 0 < β) :
    Real.rpow 2 (-log2 β - log2 (4 * ε / η ^ 2)) =
      η ^ 2 / (4 * ε * β) := by
  have ht : 0 < 4 * ε / η ^ 2 := by positivity
  calc
    Real.rpow 2 (-log2 β - log2 (4 * ε / η ^ 2)) =
        Real.rpow 2 (-log2 β + -log2 (4 * ε / η ^ 2)) := by ring_nf
    _ = Real.rpow 2 (-log2 β) * Real.rpow 2 (-log2 (4 * ε / η ^ 2)) := by
        exact Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _
    _ = β⁻¹ * (4 * ε / η ^ 2)⁻¹ := by
        rw [rpow_two_neg_log2 hβ, rpow_two_neg_log2 ht]
    _ = η ^ 2 / (4 * ε * β) := by
        field_simp [ne_of_gt hε, ne_of_gt hη, ne_of_gt hβ]

/-- Endpoint closure for a real supremum lower-bound expression embedded in
`EReal`.

If every strict lower approximation `lower < A` gives an operational lower
bound `lower - penalty`, then the endpoint `A - penalty` gives the same
operational lower bound.  This is the order-theoretic `sSup` closure used to
remove the non-attainment assumption from the one-shot HT lower-bound route. -/
theorem ereal_sub_endpoint_le_of_forall_strict_lower
    {A penalty : ℝ} {capacity : EReal}
    (h :
      ∀ lower : ℝ, lower < A →
        ((lower - penalty : ℝ) : EReal) ≤ capacity) :
    ((A - penalty : ℝ) : EReal) ≤ capacity := by
  rw [← EReal.ge_of_forall_gt_iff_ge]
  intro z hz
  have hz_real : z < A - penalty := by
    exact EReal.coe_lt_coe_iff.mp hz
  have hlower : z + penalty < A := by
    linarith
  have hcode := h (z + penalty) hlower
  have hsame : z + penalty - penalty = z := by ring
  simpa [hsame] using hcode

/-- Extended-real endpoint closure for finite strict lower approximations.

If every real `lower` strictly below an extended-real quantity `A` gives the
finite operational lower bound `lower - penalty`, then `A - penalty` is also an
operational lower bound.  This is the endpoint step needed when the source
information quantity can be `⊤`. -/
theorem ereal_sub_endpoint_le_of_forall_strict_lower_E
    {A capacity : EReal} {penalty : ℝ}
    (h :
      ∀ lower : ℝ, (lower : EReal) < A →
        ((lower - penalty : ℝ) : EReal) ≤ capacity) :
    A - (penalty : EReal) ≤ capacity := by
  rw [← EReal.ge_of_forall_gt_iff_ge]
  intro z hz
  have hzA : ((z + penalty : ℝ) : EReal) < A := by
    have hzA' : (z : EReal) + (penalty : EReal) < A :=
      EReal.add_lt_of_lt_sub hz
    simpa [EReal.coe_add] using hzA'
  have hcode := h (z + penalty) hzA
  have hsame : z + penalty - penalty = z := by ring
  simpa [hsame] using hcode

/-- Endpoint closure specialized to the barred hypothesis-testing information
lower-bound shape. -/
theorem Channel.oneShotEntanglementAssistedClassicalCapacityE_htLowerBound_endpoint
    (N : Channel a b) {ε η : ℝ}
    (hstrict :
      ∀ lower : ℝ,
        lower < N.barHypothesisTestingMutualInformationFinite (ε - η) →
          ((lower - log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
            N.oneShotEntanglementAssistedClassicalCapacityE ε) :
    ((N.barHypothesisTestingMutualInformationFinite (ε - η) -
        log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε :=
  ereal_sub_endpoint_le_of_forall_strict_lower hstrict

/-- Endpoint closure specialized to the extended-real barred
hypothesis-testing information lower-bound shape. -/
theorem Channel.oneShotEntanglementAssistedClassicalCapacityE_htLowerBound_endpoint_E
    (N : Channel a b) {ε η : ℝ}
    (hstrict :
      ∀ lower : ℝ,
        (lower : EReal) < N.barHypothesisTestingMutualInformation (ε - η) →
          ((lower - log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
            N.oneShotEntanglementAssistedClassicalCapacityE ε) :
    N.barHypothesisTestingMutualInformation (ε - η) -
        (log2 (4 * ε / η ^ 2) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε :=
  ereal_sub_endpoint_le_of_forall_strict_lower_E hstrict

/-- Finite-message rounding for the Khatri--Wilde one-shot HT lower-bound
message-size choice.

For positive `ε`, `η`, and type-II parameter `β`, there is a nonempty finite
message set size `k` such that the sequential-decoding false-alarm budget uses
only `k - 1` earlier messages while the achieved rate still lower-bounds the
source real expression.
-/
theorem exists_message_card_for_ht_lower_bound_rounding
    {ε η β : ℝ} (hε : 0 < ε) (hη : 0 < η) (hβ : 0 < β) :
    ∃ k : ℕ, 0 < k ∧
      ((k - 1 : ℕ) : ℝ) * β ≤ η ^ 2 / (4 * ε) ∧
      Real.rpow 2 (-log2 β - log2 (4 * ε / η ^ 2)) ≤ (k : ℝ) := by
  let X : ℝ := η ^ 2 / (4 * ε * β)
  have hX_pos : 0 < X := by
    unfold X
    positivity
  refine ⟨Nat.ceil X, ?_, ?_, ?_⟩
  · exact Nat.ceil_pos.mpr hX_pos
  · have hceil_lt : ((Nat.ceil X : ℕ) : ℝ) < X + 1 :=
      Nat.ceil_lt_add_one (le_of_lt hX_pos)
    have hk_pos : 0 < Nat.ceil X := Nat.ceil_pos.mpr hX_pos
    have hpred : (((Nat.ceil X - 1 : ℕ) : ℝ) : ℝ) < X := by
      rw [Nat.cast_pred hk_pos]
      linarith
    have hpred_le : (((Nat.ceil X - 1 : ℕ) : ℝ) : ℝ) ≤ X := le_of_lt hpred
    have hβ_nonneg : 0 ≤ β := le_of_lt hβ
    have hmul := mul_le_mul_of_nonneg_right hpred_le hβ_nonneg
    unfold X at hmul
    have hcalc : η ^ 2 / (4 * ε * β) * β = η ^ 2 / (4 * ε) := by
      field_simp [ne_of_gt hε, ne_of_gt hβ]
    simpa [hcalc] using hmul
  · rw [rpow_two_ht_message_budget hε hη hβ]
    exact Nat.le_ceil X

/-- If a concrete sequential decoder bounds every message error, then the
position-based protocol contributes the declared rate to one-shot
entanglement-assisted capacity. -/
theorem lowerBound_le_oneShotEntanglementAssistedClassicalCapacityE_of_sequentialDecoderError
    (P : PositionBasedCodingProtocol N M e) {seqLen : ℕ} {ε lowerBound : ℝ}
    (A :
      M → ProjectionSequence
        (Prod (TensorPower b 1) (TensorPower e (Fintype.card M))) (seqLen + 1))
    (hseq :
      ∀ m : M,
        1 - (P.decoder.prob (P.positionOutputState m) m : ℝ) ≤
          SequentialDecoding.sequenceError
            (SequentialDecoding.decoderTestSequence (A m)) (P.positionOutputState m))
    (hdec :
      ∀ m : M,
        SequentialDecoding.sequenceError
          (SequentialDecoding.decoderTestSequence (A m)) (P.positionOutputState m) ≤ ε)
    (hlower : lowerBound ≤ P.toCode.rate) :
    (lowerBound : EReal) ≤ N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  exact
    P.lowerBound_le_oneShotEntanglementAssistedClassicalCapacityE_of_positionOutput_error
      (fun m => (hseq m).trans (hdec m)) hlower

/-- Variant of the position-protocol wrapper using a finite-message
cardinality lower bound instead of a direct rate inequality. -/
theorem lowerBound_le_oneShotEntanglementAssistedClassicalCapacityE_of_sequentialDecoderError_of_rpow_two_le_card
    (P : PositionBasedCodingProtocol N M e) {seqLen : ℕ} {ε lowerBound : ℝ}
    (A :
      M → ProjectionSequence
        (Prod (TensorPower b 1) (TensorPower e (Fintype.card M))) (seqLen + 1))
    (hseq :
      ∀ m : M,
        1 - (P.decoder.prob (P.positionOutputState m) m : ℝ) ≤
          SequentialDecoding.sequenceError
            (SequentialDecoding.decoderTestSequence (A m)) (P.positionOutputState m))
    (hdec :
      ∀ m : M,
        SequentialDecoding.sequenceError
          (SequentialDecoding.decoderTestSequence (A m)) (P.positionOutputState m) ≤ ε)
    (hcard : Real.rpow 2 lowerBound ≤ (Fintype.card M : ℝ)) :
    (lowerBound : EReal) ≤ N.oneShotEntanglementAssistedClassicalCapacityE ε :=
  P.lowerBound_le_oneShotEntanglementAssistedClassicalCapacityE_of_sequentialDecoderError
    A hseq hdec (P.lowerBound_le_rate_of_rpow_two_le_card hcard)

/-- Source-shaped HT lower-bound assembly with finite-message rounding exposed
as a cardinality hypothesis.

This is the last generic bridge before inserting the canonical position-based
Naimark trace identities: missed-detection and false-alarm identities feed the
sequential decoder, while `2^lowerBound <= |M|` feeds the operational rate.
-/
theorem lowerBound_le_oneShotEntanglementAssistedClassicalCapacityE_of_ht_trace_bridges_of_rpow_two_le_card
    (P : PositionBasedCodingProtocol N M e) {testSys : Type x}
    [Fintype testSys] [DecidableEq testSys]
    {seqLen : ℕ} {ε η β lowerBound : ℝ}
    (A :
      M → ProjectionSequence
        (Prod (TensorPower b 1) (TensorPower e (Fintype.card M))) (seqLen + 1))
    {ρ σ : State testSys} (Λ : HypothesisTestingEffect ρ (ε - η))
    (hη_pos : 0 < η) (hη_lt : η < ε)
    (hseq :
      ∀ m : M,
        1 - (P.decoder.prob (P.positionOutputState m) m : ℝ) ≤
          SequentialDecoding.sequenceError
            (SequentialDecoding.decoderTestSequence (A m)) (P.positionOutputState m))
    (hmissBridge :
      ∀ m : M,
        SequentialDecoding.effectTrace (P.positionOutputState m)
            ((A m) (Fin.last seqLen)).compl.matrix ≤
          SequentialDecoding.effectTrace
            (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState ρ)
            Λ.acceptNaimarkProjection.compl.matrix)
    (hfalseBridge :
      ∀ m : M, ∀ i : Fin seqLen,
        SequentialDecoding.effectTrace (P.positionOutputState m)
            ((A m) (Fin.castSucc i)).matrix ≤
          Λ.typeIIError σ)
    (hβ : Λ.typeIIError σ ≤ β)
    (hsize : (seqLen : ℝ) * β ≤ η ^ 2 / (4 * ε))
    (hcard : Real.rpow 2 lowerBound ≤ (Fintype.card M : ℝ)) :
    (lowerBound : EReal) ≤ N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  refine
    P.lowerBound_le_oneShotEntanglementAssistedClassicalCapacityE_of_sequentialDecoderError_of_rpow_two_le_card
      A hseq ?_ hcard
  exact SequentialDecoding.decoderError_le_epsilon_of_ht_trace_bridges
    A P.positionOutputState Λ hη_pos hη_lt hmissBridge hfalseBridge hβ hsize

/-- Fixed-order sequential-decoder assembly matching the Khatri--Wilde
`i < m` proof shape.

Unlike the older generic bridge, this theorem uses one genuine decoder POVM for
all messages.  The outcome `m` is controlled by the prefix of the ordered
projectors ending at `m`, and the false-alarm contribution is summed only over
earlier positions. -/
theorem lowerBound_le_oneShotEntanglementAssistedClassicalCapacityE_of_ordered_ht_trace_bridges_of_rpow_two_le_card
    {seqLen : ℕ}
    (P : PositionBasedCodingProtocol N M e)
    {testSys : Type x} [Fintype testSys] [DecidableEq testSys]
    {ε η β lowerBound : ℝ}
    (messageIndex : M ≃ Fin (seqLen + 1))
    (_hcard_eq : Fintype.card M = seqLen + 1)
    (A :
      ProjectionSequence
        (Prod (TensorPower b 1) (TensorPower e (Fintype.card M))) (seqLen + 1))
    (hdecoder :
      ∀ m : M,
        P.decoder.effects m =
          (SequentialDecoding.sequentialDecoderPOVM A).effects (messageIndex m))
    {ρ σ : State testSys} (Λ : HypothesisTestingEffect ρ (ε - η))
    (hη_pos : 0 < η) (hη_lt : η < ε)
    (hmissBridge :
      ∀ m : M,
        SequentialDecoding.effectTrace (P.positionOutputState m)
            (A (messageIndex m)).compl.matrix ≤
          SequentialDecoding.effectTrace
            (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState ρ)
            Λ.acceptNaimarkProjection.compl.matrix)
    (hfalseBridge :
      ∀ m : M, ∀ i : Fin (messageIndex m).val,
        SequentialDecoding.effectTrace (P.positionOutputState m)
            (A ⟨i.val, by omega⟩).matrix ≤
          Λ.typeIIError σ)
    (hβ : Λ.typeIIError σ ≤ β)
    (hsize : (seqLen : ℝ) * β ≤ η ^ 2 / (4 * ε))
    (hcard : Real.rpow 2 lowerBound ≤ (Fintype.card M : ℝ)) :
    (lowerBound : EReal) ≤ N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  refine P.lowerBound_le_oneShotEntanglementAssistedClassicalCapacityE_of_positionOutput_error
    ?_ (P.lowerBound_le_rate_of_rpow_two_le_card hcard)
  intro m
  have hseq :
      1 - (P.decoder.prob (P.positionOutputState m) m : ℝ) ≤
        SequentialDecoding.sequenceError
          (SequentialDecoding.decoderTestSequence
            (SequentialDecoding.prefixProjectionSequence A (messageIndex m)))
          (P.positionOutputState m) := by
    have hprob :
        (P.decoder.prob (P.positionOutputState m) m : ℝ) =
          ((SequentialDecoding.sequentialDecoderPOVM A).prob
            (P.positionOutputState m) (messageIndex m) : ℝ) := by
      rw [POVM.prob_eq_trace_re, POVM.prob_eq_trace_re]
      rw [hdecoder m]
    rw [hprob]
    exact SequentialDecoding.sequentialDecoderPOVM_error_le_prefixSequenceError
      A (P.positionOutputState m) (messageIndex m)
  have hmiss :
      SequentialDecoding.effectTrace (P.positionOutputState m)
          ((SequentialDecoding.prefixProjectionSequence A (messageIndex m))
            (Fin.last (messageIndex m).val)).compl.matrix ≤
        ε - η := by
    have hbridge := hmissBridge m
    have hfixed := Λ.fixedNaimark_reject_le
    calc
      SequentialDecoding.effectTrace (P.positionOutputState m)
          ((SequentialDecoding.prefixProjectionSequence A (messageIndex m))
            (Fin.last (messageIndex m).val)).compl.matrix
          = SequentialDecoding.effectTrace (P.positionOutputState m)
              (A (messageIndex m)).compl.matrix := by
              simp [SequentialDecoding.prefixProjectionSequence]
      _ ≤ SequentialDecoding.effectTrace
            (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState ρ)
            Λ.acceptNaimarkProjection.compl.matrix := hbridge
      _ ≤ ε - η := hfixed
  have hfalse :
      ∀ i : Fin (messageIndex m).val,
        SequentialDecoding.effectTrace (P.positionOutputState m)
            ((SequentialDecoding.prefixProjectionSequence A (messageIndex m))
              (Fin.castSucc i)).matrix ≤ β := by
    intro i
    calc
      SequentialDecoding.effectTrace (P.positionOutputState m)
          ((SequentialDecoding.prefixProjectionSequence A (messageIndex m))
            (Fin.castSucc i)).matrix
          = SequentialDecoding.effectTrace (P.positionOutputState m)
              (A ⟨i.val, by omega⟩).matrix := by
              simp [SequentialDecoding.prefixProjectionSequence]
      _ ≤ Λ.typeIIError σ := hfalseBridge m i
      _ ≤ β := hβ
  have hβ_nonneg : 0 ≤ β :=
    (Λ.typeIIError_nonneg_htmi σ).trans hβ
  have hm_size : ((messageIndex m).val : ℝ) * β ≤ η ^ 2 / (4 * ε) := by
    have hm_le : ((messageIndex m).val : ℝ) ≤ (seqLen : ℝ) := by
      have hm_nat : (messageIndex m).val ≤ seqLen := by
        omega
      exact_mod_cast hm_nat
    exact (mul_le_mul_of_nonneg_right hm_le hβ_nonneg).trans hsize
  exact hseq.trans
    (SequentialDecoding.decoderError_le_epsilon_of_trace_bounds
      (SequentialDecoding.prefixProjectionSequence A (messageIndex m))
      (P.positionOutputState m) hη_pos hη_lt hmiss hfalse hm_size)

/-- Fixed-order sequential-decoder assembly after Naimark compression,
returned as a source-shaped one-shot achievability witness.

The projective sequential decoder lives on a larger dilation space `out`, while
the actual operational decoder is the POVM obtained by compressing it along an
isometric embedding `V`.  This is the reusable bridge needed for the
Khatri--Wilde one-shot lower-bound route: the OMW/sequential-decoding estimate
is proved in the projective Naimark space, and `compressByIsometry_prob_eq`
transfers the success probability back to the physical code.
-/
def oneShotAchievabilityWitness_of_compressed_ordered_trace_bounds_of_rpow_two_le_card
    {seqLen : ℕ} {out : Type w} [Fintype out] [DecidableEq out]
    (P : PositionBasedCodingProtocol N M e)
    {ε η β lowerBound : ℝ}
    (messageIndex : M ≃ Fin (seqLen + 1))
    (A : ProjectionSequence out (seqLen + 1))
    (V : Matrix out (Prod (TensorPower b 1) (TensorPower e (Fintype.card M))) ℂ)
    (hV : Matrix.conjTranspose V * V = 1)
    (hdecoder :
      ∀ m : M,
        P.decoder.effects m =
          ((SequentialDecoding.sequentialDecoderPOVM A).compressByIsometry V hV).effects
            (messageIndex m))
    (hη_pos : 0 < η) (hη_lt : η < ε)
    (hmiss :
      ∀ m : M,
        SequentialDecoding.effectTrace
            (POVM.isometryLiftState (P.positionOutputState m) V hV)
            (A (messageIndex m)).compl.matrix ≤ ε - η)
    (hfalse :
      ∀ m : M, ∀ i : Fin (messageIndex m).val,
        SequentialDecoding.effectTrace
            (POVM.isometryLiftState (P.positionOutputState m) V hV)
            (A ⟨i.val, by omega⟩).matrix ≤ β)
    (hβ_nonneg : 0 ≤ β)
    (hsize : (seqLen : ℝ) * β ≤ η ^ 2 / (4 * ε))
    (hcard : Real.rpow 2 lowerBound ≤ (Fintype.card M : ℝ)) :
    EntanglementAssistedOneShotAchievabilityWitness N ε lowerBound M
      (TensorPower a (Fintype.card M)) (TensorPower e (Fintype.card M)) := by
  refine P.toOneShotAchievabilityWitness ?_
    (P.lowerBound_le_rate_of_rpow_two_le_card hcard)
  refine P.maxErrorAtMost_of_positionOutput_error_le ?_
  intro m
  let lifted : State out := POVM.isometryLiftState (P.positionOutputState m) V hV
  have hseq :
      1 - (P.decoder.prob (P.positionOutputState m) m : ℝ) ≤
        SequentialDecoding.sequenceError
          (SequentialDecoding.decoderTestSequence
            (SequentialDecoding.prefixProjectionSequence A (messageIndex m)))
          lifted := by
    have hprobDecoder :
        (P.decoder.prob (P.positionOutputState m) m : ℝ) =
          (((SequentialDecoding.sequentialDecoderPOVM A).compressByIsometry V hV).prob
            (P.positionOutputState m) (messageIndex m) : ℝ) := by
      rw [POVM.prob_eq_trace_re, POVM.prob_eq_trace_re]
      rw [hdecoder m]
    have hprobCompressed :
        (((SequentialDecoding.sequentialDecoderPOVM A).compressByIsometry V hV).prob
            (P.positionOutputState m) (messageIndex m) : ℝ) =
          ((SequentialDecoding.sequentialDecoderPOVM A).prob lifted (messageIndex m) : ℝ) := by
      simpa [lifted] using
        POVM.compressByIsometry_prob_eq
          (SequentialDecoding.sequentialDecoderPOVM A) (P.positionOutputState m) V hV
          (messageIndex m)
    rw [hprobDecoder, hprobCompressed]
    exact SequentialDecoding.sequentialDecoderPOVM_error_le_prefixSequenceError
      A lifted (messageIndex m)
  have hmiss' :
      SequentialDecoding.effectTrace lifted
          ((SequentialDecoding.prefixProjectionSequence A (messageIndex m))
            (Fin.last (messageIndex m).val)).compl.matrix ≤ ε - η := by
    calc
      SequentialDecoding.effectTrace lifted
          ((SequentialDecoding.prefixProjectionSequence A (messageIndex m))
            (Fin.last (messageIndex m).val)).compl.matrix
          = SequentialDecoding.effectTrace lifted (A (messageIndex m)).compl.matrix := by
              simp [SequentialDecoding.prefixProjectionSequence]
      _ ≤ ε - η := hmiss m
  have hfalse' :
      ∀ i : Fin (messageIndex m).val,
        SequentialDecoding.effectTrace lifted
            ((SequentialDecoding.prefixProjectionSequence A (messageIndex m))
              (Fin.castSucc i)).matrix ≤ β := by
    intro i
    calc
      SequentialDecoding.effectTrace lifted
          ((SequentialDecoding.prefixProjectionSequence A (messageIndex m))
            (Fin.castSucc i)).matrix
          = SequentialDecoding.effectTrace lifted
              (A ⟨i.val, by omega⟩).matrix := by
              simp [SequentialDecoding.prefixProjectionSequence]
      _ ≤ β := hfalse m i
  have hm_size : ((messageIndex m).val : ℝ) * β ≤ η ^ 2 / (4 * ε) := by
    have hm_le : ((messageIndex m).val : ℝ) ≤ (seqLen : ℝ) := by
      have hm_nat : (messageIndex m).val ≤ seqLen := by
        omega
      exact_mod_cast hm_nat
    exact (mul_le_mul_of_nonneg_right hm_le hβ_nonneg).trans hsize
  exact hseq.trans
    (SequentialDecoding.decoderError_le_epsilon_of_trace_bounds
      (SequentialDecoding.prefixProjectionSequence A (messageIndex m))
      lifted hη_pos hη_lt hmiss' hfalse' hm_size)

/-- Fixed-order sequential-decoder assembly after Naimark compression,
returned as an extended-real capacity lower bound.

The witness-valued theorem above is the source-shaped operational statement;
this wrapper is kept for downstream capacity algebra. -/
theorem lowerBound_le_oneShotEntanglementAssistedClassicalCapacityE_of_compressed_ordered_trace_bounds_of_rpow_two_le_card
    {seqLen : ℕ} {out : Type w} [Fintype out] [DecidableEq out]
    (P : PositionBasedCodingProtocol N M e)
    {ε η β lowerBound : ℝ}
    (messageIndex : M ≃ Fin (seqLen + 1))
    (A : ProjectionSequence out (seqLen + 1))
    (V : Matrix out (Prod (TensorPower b 1) (TensorPower e (Fintype.card M))) ℂ)
    (hV : Matrix.conjTranspose V * V = 1)
    (hdecoder :
      ∀ m : M,
        P.decoder.effects m =
          ((SequentialDecoding.sequentialDecoderPOVM A).compressByIsometry V hV).effects
            (messageIndex m))
    (hη_pos : 0 < η) (hη_lt : η < ε)
    (hmiss :
      ∀ m : M,
        SequentialDecoding.effectTrace
            (POVM.isometryLiftState (P.positionOutputState m) V hV)
            (A (messageIndex m)).compl.matrix ≤ ε - η)
    (hfalse :
      ∀ m : M, ∀ i : Fin (messageIndex m).val,
        SequentialDecoding.effectTrace
            (POVM.isometryLiftState (P.positionOutputState m) V hV)
            (A ⟨i.val, by omega⟩).matrix ≤ β)
    (hβ_nonneg : 0 ≤ β)
    (hsize : (seqLen : ℝ) * β ≤ η ^ 2 / (4 * ε))
    (hcard : Real.rpow 2 lowerBound ≤ (Fintype.card M : ℝ)) :
    (lowerBound : EReal) ≤ N.oneShotEntanglementAssistedClassicalCapacityE ε :=
  QIT.EntanglementAssistedOneShotAchievabilityWitness.lowerBound_le_oneShotEntanglementAssistedClassicalCapacityE
    (P.oneShotAchievabilityWitness_of_compressed_ordered_trace_bounds_of_rpow_two_le_card
      (messageIndex := messageIndex) (A := A) (V := V) (hV := hV)
      hdecoder hη_pos hη_lt hmiss hfalse hβ_nonneg hsize hcard)

/-- Concrete canonical position-based instantiation of the one-shot
hypothesis-testing lower-bound assembly, returned as an operational witness.

The message set is any finite type explicitly ordered by
`messageIndex : M ≃ Fin (seqLen + 1)`.  The decoder is the compressed shared
Naimark dilation of the position-inserted hypothesis-testing effects, relabeled
along this order, and the trace identities from `PositionNaimarkTrace`
discharge the missed-detection and false-alarm hypotheses of the
sequential-decoding assembly. -/
def oneShotAchievabilityWitness_of_canonical_ht_effect
    {seqLen : ℕ} (ψ : PureVector (Prod a a))
    (messageIndex : M ≃ Fin (seqLen + 1))
    (hcard_eq : Fintype.card M = seqLen + 1)
    {ε η β lowerBound : ℝ}
    (Λ : HypothesisTestingEffect (N.hypothesisTestingOutputState ψ) (ε - η))
    (hη_pos : 0 < η) (hη_lt : η < ε)
    (hβ : Λ.typeIIError
        ((N.hypothesisTestingOutputState ψ).marginalA.prod
          (N.hypothesisTestingOutputState ψ).marginalB) ≤ β)
    (hβ_nonneg : 0 ≤ β)
    (hsize : (seqLen : ℝ) * β ≤ η ^ 2 / (4 * ε))
    (hcard : Real.rpow 2 lowerBound ≤ (Fintype.card M : ℝ)) :
    EntanglementAssistedOneShotAchievabilityWitness N ε lowerBound M
      (TensorPower a (Fintype.card M)) (TensorPower a (Fintype.card M)) := by
  let basePOVM :=
    positionHypothesisTestingPOVM (a := a) (b := b) Λ (Fintype.card M)
  let out := POVM.FamilyNaimarkSpace basePOVM
  let A : ProjectionSequence out (seqLen + 1) :=
    fun i =>
      positionHypothesisTestingProjection (a := a) (b := b) Λ (Fintype.card M)
        (finCongr hcard_eq.symm i)
  let V : Matrix out (Prod (TensorPower b 1) (TensorPower a (Fintype.card M))) ℂ :=
    POVM.familyNaimarkEmbedding basePOVM
  have hV : Matrix.conjTranspose V * V = 1 := by
    simpa [V, basePOVM] using POVM.familyNaimarkEmbedding_isometry basePOVM
  let decoderFin : POVM (Fin (seqLen + 1))
      (Prod (TensorPower b 1) (TensorPower a (Fintype.card M))) :=
    (SequentialDecoding.sequentialDecoderPOVM A).compressByIsometry V hV
  let decoder : POVM M (Prod (TensorPower b 1) (TensorPower a (Fintype.card M))) := {
    effects := fun m => decoderFin.effects (messageIndex m)
    pos := fun m => decoderFin.pos (messageIndex m)
    sum_eq_one := by
      change (∑ m : M, decoderFin.effects (messageIndex m)) = 1
      calc
        (∑ m : M, decoderFin.effects (messageIndex m)) =
            ∑ i : Fin (seqLen + 1), decoderFin.effects i := by
              exact Fintype.sum_equiv messageIndex
                (fun m => decoderFin.effects (messageIndex m))
                (fun i => decoderFin.effects i)
                (by intro m; rfl)
        _ = 1 := decoderFin.sum_eq_one
  }
  let messageIndexCard : M ≃ Fin (Fintype.card M) :=
    messageIndex.trans (finCongr hcard_eq.symm)
  let P : PositionBasedCodingProtocol N M a :=
    PositionBasedCodingProtocol.canonicalIndexed (N := N)
      (ψ.state.reindex (Equiv.prodComm a a))
      messageIndexCard decoder
  refine
    P.oneShotAchievabilityWitness_of_compressed_ordered_trace_bounds_of_rpow_two_le_card
      (messageIndex := messageIndex)
      (A := A) (V := V) (hV := hV) ?_ hη_pos hη_lt ?_ ?_
      hβ_nonneg hsize ?_
  · intro m
    simp [P, decoder, decoderFin]
  · intro m
    let lifted : State out := POVM.isometryLiftState (P.positionOutputState m) V hV
    have haccept :
        SequentialDecoding.effectTrace lifted (A (messageIndex m)).matrix =
          effectAcceptProbability (N.hypothesisTestingOutputState ψ) Λ.effect := by
      dsimp [lifted, P, A, V, basePOVM, messageIndexCard]
      exact
        canonicalIndexed_truePair_liftedAcceptTrace
          (N := N) (ψ := ψ)
          (messageIndex := messageIndex.trans (finCongr hcard_eq.symm))
          (Λ := Λ) (decoder := decoder) m
    have hsum :
        SequentialDecoding.effectTrace lifted (A (messageIndex m)).matrix +
          SequentialDecoding.effectTrace lifted (A (messageIndex m)).compl.matrix = 1 :=
      SequentialDecoding.effectTrace_add_compl lifted (A (messageIndex m))
    have haccept_ge :
        1 - (ε - η) ≤ SequentialDecoding.effectTrace lifted (A (messageIndex m)).matrix := by
      simpa [haccept] using Λ.accept_ge
    linarith
  · intro m i
    let lifted : State out := POVM.isometryLiftState (P.positionOutputState m) V hV
    let j : Fin (seqLen + 1) := ⟨i.val, by omega⟩
    have hi : finCongr hcard_eq.symm j ≠ messageIndexCard m := by
      intro h
      have h' : j = messageIndex m := by
        exact (finCongr hcard_eq.symm).injective h
      have hv : i.val = (messageIndex m).val := congrArg Fin.val h'
      omega
    have htrace :
        SequentialDecoding.effectTrace lifted (A j).matrix =
          Λ.typeIIError
            ((N.hypothesisTestingOutputState ψ).marginalA.prod
              (N.hypothesisTestingOutputState ψ).marginalB) := by
      dsimp [lifted, P, A, V, basePOVM, messageIndexCard, j]
      exact
        canonicalIndexed_falsePair_liftedAcceptTrace
          (N := N) (ψ := ψ)
          (messageIndex := messageIndex.trans (finCongr hcard_eq.symm))
          (Λ := Λ) (decoder := decoder) m (finCongr hcard_eq.symm j) hi
    exact htrace.le.trans hβ
  · simpa using hcard

/-- Concrete canonical position-based instantiation of the one-shot
hypothesis-testing lower-bound assembly.

This capacity-valued wrapper is retained for downstream algebra; the
witness-valued theorem above is the operational form matching the code
constructed in Khatri--Wilde's proof. -/
theorem lowerBound_le_oneShotEntanglementAssistedClassicalCapacityE_of_canonical_ht_effect
    {seqLen : ℕ} (ψ : PureVector (Prod a a))
    (messageIndex : M ≃ Fin (seqLen + 1))
    (hcard_eq : Fintype.card M = seqLen + 1)
    {ε η β lowerBound : ℝ}
    (Λ : HypothesisTestingEffect (N.hypothesisTestingOutputState ψ) (ε - η))
    (hη_pos : 0 < η) (hη_lt : η < ε)
    (hβ : Λ.typeIIError
        ((N.hypothesisTestingOutputState ψ).marginalA.prod
          (N.hypothesisTestingOutputState ψ).marginalB) ≤ β)
    (hβ_nonneg : 0 ≤ β)
    (hsize : (seqLen : ℝ) * β ≤ η ^ 2 / (4 * ε))
    (hcard : Real.rpow 2 lowerBound ≤ (Fintype.card M : ℝ)) :
    (lowerBound : EReal) ≤ N.oneShotEntanglementAssistedClassicalCapacityE ε :=
  QIT.EntanglementAssistedOneShotAchievabilityWitness.lowerBound_le_oneShotEntanglementAssistedClassicalCapacityE
    (PositionBasedCodingProtocol.oneShotAchievabilityWitness_of_canonical_ht_effect
      (N := N) (M := M) (seqLen := seqLen) ψ messageIndex hcard_eq Λ
      hη_pos hη_lt hβ hβ_nonneg hsize hcard)

end PositionBasedCodingProtocol

namespace Channel

/-- Strict-lower approximation form of the Khatri--Wilde one-shot
hypothesis-testing lower bound.

For every real `lower` strictly below the barred channel hypothesis-testing
mutual information, the position-based code constructed above achieves
`lower - log₂(4ε/η²)`.  The `hbeta_pos` hypothesis selects the finite
real-valued branch of `D_H`; a separate extended-real endpoint can remove this
branch once the zero-beta case is available. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_htLowerBound_strict
    (N : Channel a b) [Nonempty a] {ε η lower : ℝ}
    (hε_pos : 0 < ε) (hη_pos : 0 < η) (hη_lt : η < ε)
    (hlower : lower < N.barHypothesisTestingMutualInformationFinite (ε - η))
    (hbeta_pos :
      ∀ psi : PureVector (Prod a a),
        lower < N.inputBarHypothesisTestingMutualInformationFinite psi (ε - η) →
          0 <
            (N.hypothesisTestingOutputState psi).hypothesisTestingBeta
              ((N.hypothesisTestingOutputState psi).marginalA.prod
                (N.hypothesisTestingOutputState psi).marginalB)
              (ε - η)) :
    ((lower - log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  haveI : Nonempty (PureVector (Prod a a)) :=
    ⟨PureVector.basisPureVector⟩
  have htol_nonneg : 0 ≤ ε - η := le_of_lt (sub_pos.mpr hη_lt)
  obtain ⟨ψ, Λ, hΛlt⟩ :=
    N.exists_inputBarHypothesisTestingEffect_typeIIError_lt_rpow_two_neg_of_lt_Finite
      htol_nonneg hlower hbeta_pos
  let beta : ℝ := Real.rpow 2 (-lower)
  have hbeta_real_pos : 0 < beta := by
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-lower)
  have hΛle :
      Λ.typeIIError
          ((N.hypothesisTestingOutputState ψ).marginalA.prod
            (N.hypothesisTestingOutputState ψ).marginalB) ≤ beta := by
    exact le_of_lt (by simpa [beta] using hΛlt)
  obtain ⟨k, hk_pos, hsize, hcard_round⟩ :=
    PositionBasedCodingProtocol.exists_message_card_for_ht_lower_bound_rounding
      hε_pos hη_pos hbeta_real_pos
  let Message : Type u := ULift.{u} (Fin k)
  haveI : Fintype Message := inferInstance
  haveI : DecidableEq Message := inferInstance
  haveI : Nonempty Message := ⟨ULift.up ⟨0, hk_pos⟩⟩
  let seqLen : ℕ := k - 1
  have hseq_eq : seqLen + 1 = k := by
    simpa [seqLen] using Nat.succ_pred_eq_of_pos hk_pos
  let messageIndex : Message ≃ Fin (seqLen + 1) :=
    (Equiv.ulift : ULift.{u} (Fin k) ≃ Fin k).trans
      (finCongr hseq_eq.symm)
  have hcard_eq : Fintype.card Message = seqLen + 1 := by
    have hcard_ulift : Fintype.card Message = k := by
      simpa [Message] using
        Fintype.card_congr (Equiv.ulift : ULift.{u} (Fin k) ≃ Fin k)
    omega
  have hcard_code :
      Real.rpow 2 (lower - log2 (4 * ε / η ^ 2)) ≤
        (Fintype.card Message : ℝ) := by
    have hlogbeta : -log2 beta = lower := by
      have hlog : log2 beta = -lower := by
        unfold beta log2
        rw [show Real.log (Real.rpow 2 (-lower)) = (-lower) * Real.log 2 by
          exact Real.log_rpow (by norm_num : (0 : ℝ) < 2) (-lower)]
        have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
        field_simp [hlog2]
      linarith
    have hround' :
        Real.rpow 2 (lower - log2 (4 * ε / η ^ 2)) ≤ (k : ℝ) := by
      simpa [hlogbeta, sub_eq_add_neg] using hcard_round
    have hkcard : (k : ℝ) = (Fintype.card Message : ℝ) := by
      exact_mod_cast (by
        have hcard_ulift : Fintype.card Message = k := by
          simpa [Message] using
            Fintype.card_congr (Equiv.ulift : ULift.{u} (Fin k) ≃ Fin k)
        exact hcard_ulift.symm)
    simpa [hkcard] using hround'
  exact
    PositionBasedCodingProtocol.lowerBound_le_oneShotEntanglementAssistedClassicalCapacityE_of_canonical_ht_effect
      (N := N) (M := Message) (seqLen := seqLen) ψ messageIndex hcard_eq Λ
      hη_pos hη_lt hΛle (le_of_lt hbeta_real_pos) hsize hcard_code

/-- Source-shaped strict-lower operational form of the Khatri--Wilde
one-shot hypothesis-testing lower bound.

For every finite real `lower` strictly below the barred channel
hypothesis-testing mutual information, this theorem produces an actual
finite-message entanglement-assisted one-shot code whose maximal error is at
most `ε` and whose rate is at least
`lower - log₂(4ε/η²)`.  The endpoint capacity inequality is obtained from
these witnesses by the supremum closure theorem below.
-/
theorem exists_oneShotAchievabilityWitness_htLowerBound_strict_E
    (N : Channel a b) [Nonempty a] {ε η lower : ℝ}
    (hε_pos : 0 < ε) (hη_pos : 0 < η) (hη_lt : η < ε)
    (hlower : (lower : EReal) < N.barHypothesisTestingMutualInformation (ε - η)) :
    ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
      ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
        ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
          Nonempty (EntanglementAssistedOneShotAchievabilityWitness N ε
            (lower - log2 (4 * ε / η ^ 2)) M EA EB) := by
  haveI : Nonempty (PureVector (Prod a a)) :=
    ⟨PureVector.basisPureVector⟩
  have htol_nonneg : 0 ≤ ε - η := le_of_lt (sub_pos.mpr hη_lt)
  obtain ⟨ψ, Λ, hΛlt⟩ :=
    N.exists_inputBarHypothesisTestingEffect_typeIIError_lt_rpow_two_neg_of_lt
      htol_nonneg hlower
  let beta : ℝ := Real.rpow 2 (-lower)
  have hbeta_real_pos : 0 < beta := by
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-lower)
  have hΛle :
      Λ.typeIIError
          ((N.hypothesisTestingOutputState ψ).marginalA.prod
            (N.hypothesisTestingOutputState ψ).marginalB) ≤ beta := by
    exact le_of_lt (by simpa [beta] using hΛlt)
  obtain ⟨k, hk_pos, hsize, hcard_round⟩ :=
    PositionBasedCodingProtocol.exists_message_card_for_ht_lower_bound_rounding
      hε_pos hη_pos hbeta_real_pos
  let Message : Type u := ULift.{u} (Fin k)
  haveI : Fintype Message := inferInstance
  haveI : DecidableEq Message := inferInstance
  haveI : Nonempty Message := ⟨ULift.up ⟨0, hk_pos⟩⟩
  let seqLen : ℕ := k - 1
  have hseq_eq : seqLen + 1 = k := by
    simpa [seqLen] using Nat.succ_pred_eq_of_pos hk_pos
  let messageIndex : Message ≃ Fin (seqLen + 1) :=
    (Equiv.ulift : ULift.{u} (Fin k) ≃ Fin k).trans
      (finCongr hseq_eq.symm)
  have hcard_eq : Fintype.card Message = seqLen + 1 := by
    have hcard_ulift : Fintype.card Message = k := by
      simpa [Message] using
        Fintype.card_congr (Equiv.ulift : ULift.{u} (Fin k) ≃ Fin k)
    omega
  have hcard_code :
      Real.rpow 2 (lower - log2 (4 * ε / η ^ 2)) ≤
        (Fintype.card Message : ℝ) := by
    have hlogbeta : -log2 beta = lower := by
      have hlog : log2 beta = -lower := by
        unfold beta log2
        rw [show Real.log (Real.rpow 2 (-lower)) = (-lower) * Real.log 2 by
          exact Real.log_rpow (by norm_num : (0 : ℝ) < 2) (-lower)]
        have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
        field_simp [hlog2]
      linarith
    have hround' :
        Real.rpow 2 (lower - log2 (4 * ε / η ^ 2)) ≤ (k : ℝ) := by
      simpa [hlogbeta, sub_eq_add_neg] using hcard_round
    have hkcard : (k : ℝ) = (Fintype.card Message : ℝ) := by
      exact_mod_cast (by
        have hcard_ulift : Fintype.card Message = k := by
          simpa [Message] using
            Fintype.card_congr (Equiv.ulift : ULift.{u} (Fin k) ≃ Fin k)
        exact hcard_ulift.symm)
    simpa [hkcard] using hround'
  let Share : Type u := QIT.TensorPower a (Fintype.card Message)
  refine ⟨Message, inferInstance, inferInstance, inferInstance,
    Share, inferInstance, inferInstance, Share, inferInstance, inferInstance, ?_⟩
  exact ⟨
    PositionBasedCodingProtocol.oneShotAchievabilityWitness_of_canonical_ht_effect
      (N := N) (M := Message) (seqLen := seqLen) ψ messageIndex hcard_eq Λ
      hη_pos hη_lt hΛle (le_of_lt hbeta_real_pos) hsize hcard_code⟩

/-- Rate-form operational one-shot HT lower bound.

This is the same finite-message construction as
`exists_oneShotAchievabilityWitness_htLowerBound_strict_E`, with the source
penalty moved to the hypothesis.  It is convenient for downstream comparisons:
any real rate strictly below `\bar I_H^{ε-η}(N) - log₂(4ε/η²)` is achieved by
a concrete one-shot entanglement-assisted code. -/
theorem exists_oneShotAchievabilityWitness_htLowerBound_rate_strict_E
    (N : Channel a b) [Nonempty a] {ε η rate : ℝ}
    (hε_pos : 0 < ε) (hη_pos : 0 < η) (hη_lt : η < ε)
    (hrate :
      ((rate + log2 (4 * ε / η ^ 2) : ℝ) : EReal) <
        N.barHypothesisTestingMutualInformation (ε - η)) :
    ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
      ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
        ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
          Nonempty (EntanglementAssistedOneShotAchievabilityWitness N ε rate M EA EB) := by
  obtain ⟨M, hMft, hMeq, hMne, EA, hEAft, hEAeq, EB, hEBft, hEBeq, hW⟩ :=
    N.exists_oneShotAchievabilityWitness_htLowerBound_strict_E
      hε_pos hη_pos hη_lt hrate
  letI : Fintype M := hMft
  letI : DecidableEq M := hMeq
  letI : Nonempty M := hMne
  letI : Fintype EA := hEAft
  letI : DecidableEq EA := hEAeq
  letI : Fintype EB := hEBft
  letI : DecidableEq EB := hEBeq
  rcases hW with ⟨W⟩
  refine ⟨M, hMft, hMeq, hMne, EA, hEAft, hEAeq, EB, hEBft, hEBeq, ?_⟩
  have hsame :
      rate + log2 (4 * ε / η ^ 2) - log2 (4 * ε / η ^ 2) = rate := by
    ring
  exact ⟨{
    code := W.code
    maxError_le := W.maxError_le
    lowerBound_le_rate := by
      simpa [hsame] using W.lowerBound_le_rate
  }⟩

/-- Strict-lower approximation form of the Khatri--Wilde one-shot
hypothesis-testing lower bound with the source-faithful extended-real barred
information quantity.

This version removes the positive-beta side condition from the real-valued
branch: any finite real `lower` strictly below the extended-real
`\bar I_H^{ε-η}(N)` has a concrete hypothesis-testing effect with type-II error
below `2^{-lower}`, including the zero-beta branch where the information value
is `⊤`. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_htLowerBound_strict_E
    (N : Channel a b) [Nonempty a] {ε η lower : ℝ}
    (hε_pos : 0 < ε) (hη_pos : 0 < η) (hη_lt : η < ε)
    (hlower : (lower : EReal) < N.barHypothesisTestingMutualInformation (ε - η)) :
    ((lower - log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  haveI : Nonempty (PureVector (Prod a a)) :=
    ⟨PureVector.basisPureVector⟩
  have htol_nonneg : 0 ≤ ε - η := le_of_lt (sub_pos.mpr hη_lt)
  obtain ⟨ψ, Λ, hΛlt⟩ :=
    N.exists_inputBarHypothesisTestingEffect_typeIIError_lt_rpow_two_neg_of_lt
      htol_nonneg hlower
  let beta : ℝ := Real.rpow 2 (-lower)
  have hbeta_real_pos : 0 < beta := by
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-lower)
  have hΛle :
      Λ.typeIIError
          ((N.hypothesisTestingOutputState ψ).marginalA.prod
            (N.hypothesisTestingOutputState ψ).marginalB) ≤ beta := by
    exact le_of_lt (by simpa [beta] using hΛlt)
  obtain ⟨k, hk_pos, hsize, hcard_round⟩ :=
    PositionBasedCodingProtocol.exists_message_card_for_ht_lower_bound_rounding
      hε_pos hη_pos hbeta_real_pos
  let Message : Type u := ULift.{u} (Fin k)
  haveI : Fintype Message := inferInstance
  haveI : DecidableEq Message := inferInstance
  haveI : Nonempty Message := ⟨ULift.up ⟨0, hk_pos⟩⟩
  let seqLen : ℕ := k - 1
  have hseq_eq : seqLen + 1 = k := by
    simpa [seqLen] using Nat.succ_pred_eq_of_pos hk_pos
  let messageIndex : Message ≃ Fin (seqLen + 1) :=
    (Equiv.ulift : ULift.{u} (Fin k) ≃ Fin k).trans
      (finCongr hseq_eq.symm)
  have hcard_eq : Fintype.card Message = seqLen + 1 := by
    have hcard_ulift : Fintype.card Message = k := by
      simpa [Message] using
        Fintype.card_congr (Equiv.ulift : ULift.{u} (Fin k) ≃ Fin k)
    omega
  have hcard_code :
      Real.rpow 2 (lower - log2 (4 * ε / η ^ 2)) ≤
        (Fintype.card Message : ℝ) := by
    have hlogbeta : -log2 beta = lower := by
      have hlog : log2 beta = -lower := by
        unfold beta log2
        rw [show Real.log (Real.rpow 2 (-lower)) = (-lower) * Real.log 2 by
          exact Real.log_rpow (by norm_num : (0 : ℝ) < 2) (-lower)]
        have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
        field_simp [hlog2]
      linarith
    have hround' :
        Real.rpow 2 (lower - log2 (4 * ε / η ^ 2)) ≤ (k : ℝ) := by
      simpa [hlogbeta, sub_eq_add_neg] using hcard_round
    have hkcard : (k : ℝ) = (Fintype.card Message : ℝ) := by
      exact_mod_cast (by
        have hcard_ulift : Fintype.card Message = k := by
          simpa [Message] using
            Fintype.card_congr (Equiv.ulift : ULift.{u} (Fin k) ≃ Fin k)
        exact hcard_ulift.symm)
    simpa [hkcard] using hround'
  exact
    PositionBasedCodingProtocol.lowerBound_le_oneShotEntanglementAssistedClassicalCapacityE_of_canonical_ht_effect
      (N := N) (M := Message) (seqLen := seqLen) ψ messageIndex hcard_eq Λ
      hη_pos hη_lt hΛle (le_of_lt hbeta_real_pos) hsize hcard_code

/-- Khatri--Wilde one-shot hypothesis-testing lower bound for
entanglement-assisted classical communication.

This is the source-shaped extended-real formulation:
`C_EA^ε(N) ≥ \bar I_H^{ε-η}(N) - log₂(4ε/η²)` for `0 < η < ε`. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_htLowerBound
    (N : Channel a b) [Nonempty a] {ε η : ℝ}
    (hε_pos : 0 < ε) (hη_pos : 0 < η) (hη_lt : η < ε) :
    N.barHypothesisTestingMutualInformation (ε - η) -
        (log2 (4 * ε / η ^ 2) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε :=
  QIT.PositionBasedCodingProtocol.Channel.oneShotEntanglementAssistedClassicalCapacityE_htLowerBound_endpoint_E
    N
    (fun _ hlower =>
      N.oneShotEntanglementAssistedClassicalCapacityE_htLowerBound_strict_E
        hε_pos hη_pos hη_lt hlower)

/-- Endpoint form of the Khatri--Wilde one-shot hypothesis-testing lower bound
on the finite real-valued branch.

This theorem packages the strict-lower approximation theorem with the
order-theoretic endpoint closure.  The remaining hypothesis records the exact
place where the current real-valued `D_H` API excludes the zero-beta
extended-real branch. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_htLowerBound_endpoint_of_beta_pos
    (N : Channel a b) [Nonempty a] {ε η : ℝ}
    (hε_pos : 0 < ε) (hη_pos : 0 < η) (hη_lt : η < ε)
    (hbeta_pos :
      ∀ lower : ℝ, ∀ psi : PureVector (Prod a a),
        lower < N.inputBarHypothesisTestingMutualInformationFinite psi (ε - η) →
          0 <
            (N.hypothesisTestingOutputState psi).hypothesisTestingBeta
              ((N.hypothesisTestingOutputState psi).marginalA.prod
                (N.hypothesisTestingOutputState psi).marginalB)
              (ε - η)) :
    ((N.barHypothesisTestingMutualInformationFinite (ε - η) -
        log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε :=
  QIT.PositionBasedCodingProtocol.Channel.oneShotEntanglementAssistedClassicalCapacityE_htLowerBound_endpoint
    N
    (fun lower hlower =>
      N.oneShotEntanglementAssistedClassicalCapacityE_htLowerBound_strict
        hε_pos hη_pos hη_lt hlower (hbeta_pos lower))

end Channel

end

end QIT
