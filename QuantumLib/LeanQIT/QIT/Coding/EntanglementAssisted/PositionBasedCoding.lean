/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Basic
public import QIT.Symmetry.SymmetricSubspace

/-!
# Position-based coding

This module records the source-shaped position-based coding construction used
in the one-shot lower-bound route for entanglement-assisted classical
communication [KhatriWilde2024Principles, Chapters/EA_capacity.tex:530-665].

The construction starts from `|M|` shared copies of a bipartite state, uses a
message-indexed encoder selecting the transmitted position, and packages the
result as an operational one-shot entanglement-assisted classical code.  The
sequential-decoding projectors, Hayashi--Nagaoka estimate, and numerical
one-shot lower bound are separate proof layers.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace TensorPower

/-- The complement index family of a distinguished tensor-power coordinate. -/
abbrev CoordComplement (k : ℕ) (m : Fin k) :=
  {i : Fin k // i ≠ m} → a

/-- Split a function on `Fin k` into one distinguished coordinate and the
remaining coordinates. -/
def finFunctionCoordSplitEquiv (k : ℕ) (m : Fin k) :
    (Fin k → a) ≃ Prod (TensorPower a 1) (CoordComplement (a := a) k m) where
  toFun f := ((f m, PUnit.unit), fun i => f i.1)
  invFun y := fun i => if h : i = m then y.1.1 else y.2 ⟨i, h⟩
  left_inv f := by
    funext i
    by_cases h : i = m
    · subst h
      simp
    · simp [h]
  right_inv y := by
    rcases y with ⟨⟨ya, yu⟩, ytail⟩
    cases yu
    apply Prod.ext
    · simp
    · funext i
      simp [i.2]

/-- Split a tensor power into one distinguished coordinate and all remaining
coordinates.  The one-coordinate output is kept in the project's
`TensorPower a 1` convention so it can be used as a one-use channel input. -/
def coordSplitEquiv (k : ℕ) (m : Fin k) :
    TensorPower a k ≃ Prod (TensorPower a 1) (CoordComplement (a := a) k m) :=
  (tensorPowerEquiv (a := a) k).trans (finFunctionCoordSplitEquiv (a := a) k m)

omit [Fintype a] [DecidableEq a] in
@[simp]
theorem coordSplitEquiv_apply_fst
    (k : ℕ) (m : Fin k) (x : TensorPower a k) :
    ((coordSplitEquiv (a := a) k m x).1).1 =
      tensorPowerEquiv (a := a) k x m :=
  rfl

omit [Fintype a] [DecidableEq a] in
@[simp]
theorem coordSplitEquiv_apply_snd
    (k : ℕ) (m : Fin k) (x : TensorPower a k)
    (i : {i : Fin k // i ≠ m}) :
    (coordSplitEquiv (a := a) k m x).2 i =
      tensorPowerEquiv (a := a) k x i.1 :=
  rfl

omit [Fintype a] [DecidableEq a] in
@[simp]
theorem coordSplitEquiv_symm_apply_fst
    (k : ℕ) (m : Fin k)
    (x : TensorPower a 1) (tail : CoordComplement (a := a) k m) :
    tensorPowerEquiv (a := a) k
        ((coordSplitEquiv (a := a) k m).symm (x, tail)) m = x.1 := by
  cases x with
  | mk xa xu =>
      cases xu
      simp [coordSplitEquiv, finFunctionCoordSplitEquiv]

omit [Fintype a] [DecidableEq a] in
@[simp]
theorem coordSplitEquiv_symm_apply_snd
    (k : ℕ) (m : Fin k)
    (x : TensorPower a 1) (tail : CoordComplement (a := a) k m)
    (i : {i : Fin k // i ≠ m}) :
    tensorPowerEquiv (a := a) k
        ((coordSplitEquiv (a := a) k m).symm (x, tail)) i.1 = tail i := by
  cases x with
  | mk xa xu =>
      cases xu
      simp [coordSplitEquiv, finFunctionCoordSplitEquiv, i.2]

end TensorPower

namespace Channel

/-- Kraus operator for selecting one tensor-power coordinate and tracing out
all other coordinates. -/
def positionSelectionKraus (k : ℕ) (m : Fin k)
    (tail : TensorPower.CoordComplement (a := a) k m) :
    Matrix (QIT.TensorPower a 1) (QIT.TensorPower a k) ℂ :=
  fun out inp =>
    if TensorPower.coordSplitEquiv (a := a) k m inp = (out, tail) then 1 else 0

omit [Fintype a] in theorem positionSelectionKraus_apply (k : ℕ) (m : Fin k)
    (tail : TensorPower.CoordComplement (a := a) k m)
    (out : QIT.TensorPower a 1) (inp : QIT.TensorPower a k) :
    positionSelectionKraus (a := a) k m tail out inp =
      if TensorPower.coordSplitEquiv (a := a) k m inp = (out, tail) then 1 else 0 :=
  rfl

/-- Matrix map selecting a distinguished tensor-power coordinate and discarding
the rest.  It is written in Kraus form, hence completely positive. -/
def positionSelectionMap (k : ℕ) (m : Fin k) :
    MatrixMap (QIT.TensorPower a k) (QIT.TensorPower a 1) :=
  MatrixMap.ofKraus (positionSelectionKraus (a := a) k m)

theorem positionSelectionMap_isCompletelyPositive (k : ℕ) (m : Fin k) :
    MatrixMap.IsCompletelyPositive (positionSelectionMap (a := a) k m) := by
  unfold positionSelectionMap
  rw [MatrixMap.IsCompletelyPositive, MatrixMap.choi_ofKraus]
  exact Matrix.posSemidef_sum Finset.univ fun tail _ =>
    Matrix.posSemidef_vecMulVec_self_star
      (fun x : QIT.TensorPower a k × QIT.TensorPower a 1 =>
        positionSelectionKraus (a := a) k m tail x.2 x.1)

theorem positionSelectionMap_tracePreserving (k : ℕ) (m : Fin k) :
    MatrixMap.IsTracePreserving (positionSelectionMap (a := a) k m) := by
  intro X
  let K := positionSelectionKraus (a := a) k m
  have hAdj : MatrixMap.krausAdjoint K (1 : CMatrix (QIT.TensorPower a 1)) =
      (1 : CMatrix (QIT.TensorPower a k)) := by
    ext i j
    unfold MatrixMap.krausAdjoint
    simp only [Matrix.mul_one]
    by_cases hij : i = j
    · subst hij
      let split := TensorPower.coordSplitEquiv (a := a) k m i
      have hsplit0 : TensorPower.coordSplitEquiv (a := a) k m i = split := rfl
      rcases split with ⟨out, tail⟩
      have hsplit : TensorPower.coordSplitEquiv (a := a) k m i = (out, tail) := hsplit0
      rw [Matrix.sum_apply]
      simp only [Matrix.one_apply_eq]
      change (∑ tail' : TensorPower.CoordComplement (a := a) k m,
          ((K tail').conjTranspose * K tail') i i) = (1 : ℂ)
      rw [Finset.sum_eq_single tail]
      · change (∑ out' : QIT.TensorPower a 1,
            star (K tail out' i) * K tail out' i) = (1 : ℂ)
        rw [Finset.sum_eq_single out]
        · simp [K, positionSelectionKraus, hsplit]
        · intro out' _ hout'
          have hneq : TensorPower.coordSplitEquiv (a := a) k m i ≠ (out', tail) := by
            intro h
            have hout_eq : out = out' := congrArg Prod.fst (hsplit.symm.trans h)
            exact hout' hout_eq.symm
          simp [K, positionSelectionKraus, hneq]
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ _))
      · intro tail' _ htail'
        change ((K tail').conjTranspose * K tail') i i = 0
        change (∑ out' : QIT.TensorPower a 1,
            star (K tail' out' i) * K tail' out' i) = (0 : ℂ)
        apply Finset.sum_eq_zero
        intro out' _
        have hneq : TensorPower.coordSplitEquiv (a := a) k m i ≠ (out', tail') := by
          intro h
          have htail_eq : tail = tail' := congrArg Prod.snd (hsplit.symm.trans h)
          exact htail' htail_eq.symm
        simp [K, positionSelectionKraus, hneq]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    · have hzero :
          ∀ tail : TensorPower.CoordComplement (a := a) k m,
            ∀ out : QIT.TensorPower a 1,
              ¬ (TensorPower.coordSplitEquiv (a := a) k m i = (out, tail) ∧
                TensorPower.coordSplitEquiv (a := a) k m j = (out, tail)) := by
        intro tail out hp
        exact hij ((TensorPower.coordSplitEquiv (a := a) k m).injective
          (hp.1.trans hp.2.symm))
      rw [Matrix.one_apply_ne hij]
      rw [Matrix.sum_apply]
      change (∑ tail : TensorPower.CoordComplement (a := a) k m,
          ((K tail).conjTranspose * K tail) i j) = (0 : ℂ)
      apply Finset.sum_eq_zero
      intro tail _
      change (∑ out : QIT.TensorPower a 1,
          star (K tail out i) * K tail out j) = (0 : ℂ)
      apply Finset.sum_eq_zero
      intro out _
      by_cases hi : TensorPower.coordSplitEquiv (a := a) k m i = (out, tail)
      · have hj : TensorPower.coordSplitEquiv (a := a) k m j ≠ (out, tail) := by
          intro hj
          exact hij ((TensorPower.coordSplitEquiv (a := a) k m).injective (hi.trans hj.symm))
        have hjK : K tail out j = 0 := by
          simp [K, positionSelectionKraus, hj]
        simp [hjK]
      · have hiK : K tail out i = 0 := by
          simp [K, positionSelectionKraus, hi]
        simp [hiK]
  have hdual := MatrixMap.ofKraus_trace_duality K X (1 : CMatrix (QIT.TensorPower a 1))
  simpa [positionSelectionMap, K, hAdj] using hdual

/-- Channel selecting one tensor-power coordinate and discarding all other
coordinates.  This is the encoder primitive in Khatri--Wilde
position-based coding. -/
def positionSelection (k : ℕ) (m : Fin k) :
    Channel (QIT.TensorPower a k) (QIT.TensorPower a 1) where
  map := positionSelectionMap (a := a) k m
  completelyPositive := positionSelectionMap_isCompletelyPositive (a := a) k m
  tracePreserving := positionSelectionMap_tracePreserving (a := a) k m
  mapsPositive :=
    MatrixMap.isCompletelyPositive_mapsPositive (positionSelectionMap (a := a) k m)
      (positionSelectionMap_isCompletelyPositive (a := a) k m)

@[simp]
theorem positionSelection_map (k : ℕ) (m : Fin k) :
    (positionSelection (a := a) k m).map = positionSelectionMap (a := a) k m :=
  rfl

end Channel

namespace Channel

variable (N : Channel a b)

/-- Candidate rates attained by one-shot `ε`-reliable
entanglement-assisted classical codes. -/
def oneShotEntanglementAssistedClassicalRateSet (ε : ℝ) : Set ℝ :=
  {R : ℝ |
    ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
      ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
        ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
          ∃ C : EntanglementAssistedClassicalCode N 1 M EA EB,
            C.maxErrorAtMost ε ∧ R = C.rate}

theorem oneShotEntanglementAssistedClassicalCapacityFinite_eq_sSup (ε : ℝ) :
    N.oneShotEntanglementAssistedClassicalCapacityFinite ε =
      sSup (N.oneShotEntanglementAssistedClassicalRateSet ε) :=
  rfl

end Channel

/-- Source-shaped one-shot position-based coding protocol.

The Bob-side type `e` is the one-copy retained share.  The shared state used by
the operational code is `sourceState.tensorPowerBipartite |M|`, i.e. `|M|`
copies of the source bipartite state, split into Alice and Bob tensor powers.
For each message, the encoder is required to produce the declared
`encodedPositionState`; this is the Lean interface corresponding to sending
the selected position through the channel. -/
structure PositionBasedCodingProtocol (N : Channel a b)
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (e : Type u) [Fintype e] [DecidableEq e] where
  sourceState : State (Prod a e)
  encoder :
    M → Channel (TensorPower a (Fintype.card M)) (TensorPower a 1)
  decoder : POVM M (Prod (TensorPower b 1) (TensorPower e (Fintype.card M)))
  encodedPositionState :
    M → State (Prod (TensorPower a 1) (TensorPower e (Fintype.card M)))
  encoder_eq_position :
    ∀ m : M,
      ((encoder m).prod (Channel.idChannel (TensorPower e (Fintype.card M)))).applyState
        (sourceState.tensorPowerBipartite (Fintype.card M)) =
          encodedPositionState m

namespace PositionBasedCodingProtocol

variable {N : Channel a b}
variable {M : Type u} [Fintype M] [DecidableEq M] [Nonempty M]
variable {e : Type u} [Fintype e] [DecidableEq e]

/-- Canonical position-based protocol indexed by an explicit bijection from
messages to positions.  The encoder for message `m` selects the
`messageIndex m` Alice tensor-power coordinate and discards the remaining
Alice shares; Bob keeps the full tensor-power reference side.

This is the source-faithful constructor used by the Khatri--Wilde
position-based one-shot lower-bound route.  It deliberately uses the
coordinate-selection channel above, rather than a prepare channel, so the
input-reference correlation in the selected copy is preserved. -/
def canonicalIndexed
    (sourceState : State (Prod a e))
    (messageIndex : M ≃ Fin (Fintype.card M))
    (decoder : POVM M (Prod (TensorPower b 1) (TensorPower e (Fintype.card M)))) :
    PositionBasedCodingProtocol N M e where
  sourceState := sourceState
  encoder := fun m =>
    Channel.positionSelection (a := a) (Fintype.card M) (messageIndex m)
  decoder := decoder
  encodedPositionState := fun m =>
    (((Channel.positionSelection (a := a) (Fintype.card M) (messageIndex m)).prod
      (Channel.idChannel (TensorPower e (Fintype.card M)))).applyState
        (sourceState.tensorPowerBipartite (Fintype.card M)))
  encoder_eq_position := by
    intro m
    rfl

@[simp]
theorem canonicalIndexed_sourceState
    (sourceState : State (Prod a e))
    (messageIndex : M ≃ Fin (Fintype.card M))
    (decoder : POVM M (Prod (TensorPower b 1) (TensorPower e (Fintype.card M)))) :
    (canonicalIndexed (N := N) sourceState messageIndex decoder).sourceState =
      sourceState :=
  rfl

@[simp]
theorem canonicalIndexed_encoder
    (sourceState : State (Prod a e))
    (messageIndex : M ≃ Fin (Fintype.card M))
    (decoder : POVM M (Prod (TensorPower b 1) (TensorPower e (Fintype.card M))))
    (m : M) :
    (canonicalIndexed (N := N) sourceState messageIndex decoder).encoder m =
      Channel.positionSelection (a := a) (Fintype.card M) (messageIndex m) :=
  rfl

@[simp]
theorem canonicalIndexed_decoder
    (sourceState : State (Prod a e))
    (messageIndex : M ≃ Fin (Fintype.card M))
    (decoder : POVM M (Prod (TensorPower b 1) (TensorPower e (Fintype.card M)))) :
    (canonicalIndexed (N := N) sourceState messageIndex decoder).decoder = decoder :=
  rfl

@[simp]
theorem canonicalIndexed_encodedPositionState
    (sourceState : State (Prod a e))
    (messageIndex : M ≃ Fin (Fintype.card M))
    (decoder : POVM M (Prod (TensorPower b 1) (TensorPower e (Fintype.card M))))
    (m : M) :
    (canonicalIndexed (N := N) sourceState messageIndex decoder).encodedPositionState m =
      (((Channel.positionSelection (a := a) (Fintype.card M) (messageIndex m)).prod
        (Channel.idChannel (TensorPower e (Fintype.card M)))).applyState
          (sourceState.tensorPowerBipartite (Fintype.card M))) :=
  rfl

/-- The operational one-shot entanglement-assisted code induced by a
position-based coding protocol. -/
def toCode (P : PositionBasedCodingProtocol N M e) :
    EntanglementAssistedClassicalCode N 1 M
      (TensorPower a (Fintype.card M)) (TensorPower e (Fintype.card M)) where
  sharedState := P.sourceState.tensorPowerBipartite (Fintype.card M)
  encoder := P.encoder
  decoder := P.decoder

@[simp]
theorem toCode_sharedState (P : PositionBasedCodingProtocol N M e) :
    P.toCode.sharedState = P.sourceState.tensorPowerBipartite (Fintype.card M) :=
  rfl

@[simp]
theorem toCode_encoder (P : PositionBasedCodingProtocol N M e) :
    P.toCode.encoder = P.encoder :=
  rfl

@[simp]
theorem toCode_decoder (P : PositionBasedCodingProtocol N M e) :
    P.toCode.decoder = P.decoder :=
  rfl

/-- The encoded channel-input/Bob-side state is the declared position state. -/
theorem channelInputState_eq_position
    (P : PositionBasedCodingProtocol N M e) (m : M) :
    P.toCode.channelInputState m = P.encodedPositionState m := by
  exact P.encoder_eq_position m

/-- Bob's pre-decoding state after the selected position is sent through the
channel. -/
def positionOutputState (P : PositionBasedCodingProtocol N M e) (m : M) :
    State (Prod (TensorPower b 1) (TensorPower e (Fintype.card M))) :=
  ((N.tensorPower 1).prod (Channel.idChannel (TensorPower e (Fintype.card M)))).applyState
    (P.encodedPositionState m)

/-- The operational output state of the induced code is the position-output
state. -/
theorem outputState_eq_positionOutput
    (P : PositionBasedCodingProtocol N M e) (m : M) :
    P.toCode.outputState m = P.positionOutputState m := by
  unfold EntanglementAssistedClassicalCode.outputState positionOutputState
  rw [P.channelInputState_eq_position m]

/-- Channel-input state of the canonical position-based protocol. -/
@[simp]
theorem canonicalIndexed_channelInputState
    (sourceState : State (Prod a e))
    (messageIndex : M ≃ Fin (Fintype.card M))
    (decoder : POVM M (Prod (TensorPower b 1) (TensorPower e (Fintype.card M))))
    (m : M) :
    (canonicalIndexed (N := N) sourceState messageIndex decoder).toCode.channelInputState m =
      (((Channel.positionSelection (a := a) (Fintype.card M) (messageIndex m)).prod
        (Channel.idChannel (TensorPower e (Fintype.card M)))).applyState
          (sourceState.tensorPowerBipartite (Fintype.card M))) :=
  rfl

/-- Channel-output state of the canonical position-based protocol after the
selected input share is sent through `N`. -/
@[simp]
theorem canonicalIndexed_positionOutputState
    (sourceState : State (Prod a e))
    (messageIndex : M ≃ Fin (Fintype.card M))
    (decoder : POVM M (Prod (TensorPower b 1) (TensorPower e (Fintype.card M))))
    (m : M) :
    (canonicalIndexed (N := N) sourceState messageIndex decoder).positionOutputState m =
      ((N.tensorPower 1).prod (Channel.idChannel (TensorPower e (Fintype.card M)))).applyState
        (((Channel.positionSelection (a := a) (Fintype.card M) (messageIndex m)).prod
          (Channel.idChannel (TensorPower e (Fintype.card M)))).applyState
            (sourceState.tensorPowerBipartite (Fintype.card M))) :=
  rfl

/-- Success probability of the induced code, written with the position-output
state. -/
theorem successProbability_eq_positionOutput
    (P : PositionBasedCodingProtocol N M e) (m : M) :
    P.toCode.successProbability m =
      (P.decoder.prob (P.positionOutputState m) m : ℝ) := by
  unfold EntanglementAssistedClassicalCode.successProbability
  rw [P.outputState_eq_positionOutput m]
  rfl

/-- Message-wise error of the induced code, written with the position-output
state. -/
theorem error_eq_positionOutput
    (P : PositionBasedCodingProtocol N M e) (m : M) :
    P.toCode.error m =
      1 - (P.decoder.prob (P.positionOutputState m) m : ℝ) := by
  unfold EntanglementAssistedClassicalCode.error
  rw [P.successProbability_eq_positionOutput m]

/-- A message-wise decoder-error estimate for the position-output states gives
the operational maximal-error condition for the induced one-shot code. -/
theorem maxErrorAtMost_of_positionOutput_error_le
    (P : PositionBasedCodingProtocol N M e) {ε : ℝ}
    (herror :
      ∀ m : M, 1 - (P.decoder.prob (P.positionOutputState m) m : ℝ) ≤ ε) :
    P.toCode.maxErrorAtMost ε := by
  intro m
  rw [P.error_eq_positionOutput m]
  exact herror m

/-- One-shot position-based codes have rate `log_2 |M|`. -/
theorem rate_eq_log_card (P : PositionBasedCodingProtocol N M e) :
    P.toCode.rate = log2 (Fintype.card M : ℝ) := by
  unfold EntanglementAssistedClassicalCode.rate entanglementAssistedMessageRate
  norm_num

/-- A reliable position-based code contributes its rate to the one-shot
capacity candidate set. -/
theorem rate_mem_oneShotEntanglementAssistedClassicalRateSet
    (P : PositionBasedCodingProtocol N M e) {ε : ℝ}
    (hε : P.toCode.maxErrorAtMost ε) :
    P.toCode.rate ∈ N.oneShotEntanglementAssistedClassicalRateSet ε := by
  unfold Channel.oneShotEntanglementAssistedClassicalRateSet
  exact ⟨M, inferInstance, inferInstance, inferInstance,
    TensorPower a (Fintype.card M), inferInstance, inferInstance,
    TensorPower e (Fintype.card M), inferInstance, inferInstance,
    P.toCode, hε, rfl⟩

/-- Convert a position-based protocol with the needed reliability and rate
estimate into the one-shot achievability witness consumed by the lower-bound
assembly layer. -/
def toOneShotAchievabilityWitness
    (P : PositionBasedCodingProtocol N M e) {ε lowerBound : ℝ}
    (hε : P.toCode.maxErrorAtMost ε)
    (hlower : lowerBound ≤ P.toCode.rate) :
    EntanglementAssistedOneShotAchievabilityWitness N ε lowerBound M
      (TensorPower a (Fintype.card M)) (TensorPower e (Fintype.card M)) where
  code := P.toCode
  maxError_le := hε
  lowerBound_le_rate := hlower

@[simp]
theorem toOneShotAchievabilityWitness_code
    (P : PositionBasedCodingProtocol N M e) {ε lowerBound : ℝ}
    (hε : P.toCode.maxErrorAtMost ε)
    (hlower : lowerBound ≤ P.toCode.rate) :
    (P.toOneShotAchievabilityWitness hε hlower).code = P.toCode :=
  rfl

/-- Final operational assembly for a position-based one-shot lower-bound
proof: message-wise decoder-error estimates plus a rate-rounding inequality
produce the extended-real capacity lower bound.

The source-specific work remains in the hypotheses: for Khatri--Wilde's
theorem these are supplied by the canonical position-based output trace
identities, sequential-decoding estimate, and message-size rounding. -/
theorem lowerBound_le_oneShotEntanglementAssistedClassicalCapacityE_of_positionOutput_error
    (P : PositionBasedCodingProtocol N M e) {ε lowerBound : ℝ}
    (herror :
      ∀ m : M, 1 - (P.decoder.prob (P.positionOutputState m) m : ℝ) ≤ ε)
    (hlower : lowerBound ≤ P.toCode.rate) :
    (lowerBound : EReal) ≤ N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  have hε : P.toCode.maxErrorAtMost ε :=
    P.maxErrorAtMost_of_positionOutput_error_le herror
  unfold Channel.oneShotEntanglementAssistedClassicalCapacityE
  calc
    (lowerBound : EReal) ≤ (P.toCode.rate : EReal) := by
      exact_mod_cast hlower
    _ ≤ sSup {R : EReal |
          ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
            ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
              ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
                ∃ C : EntanglementAssistedClassicalCode N 1 M EA EB,
                  C.maxErrorAtMost ε ∧ R = (C.rate : EReal)} := by
        exact le_sSup ⟨M, inferInstance, inferInstance, inferInstance,
          TensorPower a (Fintype.card M), inferInstance, inferInstance,
          TensorPower e (Fintype.card M), inferInstance, inferInstance,
          P.toCode, hε, rfl⟩

end PositionBasedCodingProtocol

namespace EntanglementAssistedOneShotAchievabilityWitness

variable {N : Channel a b}
variable {M : Type u} [Fintype M] [DecidableEq M] [Nonempty M]
variable {EA : Type u} [Fintype EA] [DecidableEq EA]
variable {EB : Type u} [Fintype EB] [DecidableEq EB]

/-- A one-shot achievability witness contributes its code rate to the real
one-shot rate candidate set. -/
theorem rate_mem_oneShotEntanglementAssistedClassicalRateSet
    {ε lowerBound : ℝ}
    (W : EntanglementAssistedOneShotAchievabilityWitness N ε lowerBound M EA EB) :
    W.code.rate ∈ N.oneShotEntanglementAssistedClassicalRateSet ε := by
  unfold Channel.oneShotEntanglementAssistedClassicalRateSet
  exact ⟨M, inferInstance, inferInstance, inferInstance,
    EA, inferInstance, inferInstance, EB, inferInstance, inferInstance,
    W.code, W.maxError_le, rfl⟩

/-- A one-shot achievability witness lower-bounds the extended-real one-shot
capacity.  This is the unconditional supremum bridge used by source-shaped
one-shot lower-bound proofs. -/
theorem lowerBound_le_oneShotEntanglementAssistedClassicalCapacityE
    {ε lowerBound : ℝ}
    (W : EntanglementAssistedOneShotAchievabilityWitness N ε lowerBound M EA EB) :
    (lowerBound : EReal) ≤ N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  unfold Channel.oneShotEntanglementAssistedClassicalCapacityE
  calc
    (lowerBound : EReal) ≤ (W.code.rate : EReal) := by
      exact_mod_cast W.lowerBound_le_rate
    _ ≤ sSup {R : EReal |
          ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
            ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
              ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
                ∃ C : EntanglementAssistedClassicalCode N 1 M EA EB,
                  C.maxErrorAtMost ε ∧ R = (C.rate : EReal)} := by
        exact le_sSup ⟨M, inferInstance, inferInstance, inferInstance,
          EA, inferInstance, inferInstance, EB, inferInstance, inferInstance,
          W.code, W.maxError_le, rfl⟩

/-- Real-valued one-shot capacity lower bridge, assuming the real rate set has
an upper bound.  In the source proof this boundedness is supplied by the
one-shot converse; the extended-real bridge above is unconditional. -/
theorem lowerBound_le_oneShotEntanglementAssistedClassicalCapacityFinite_of_bddAbove
    {ε lowerBound : ℝ}
    (W : EntanglementAssistedOneShotAchievabilityWitness N ε lowerBound M EA EB)
    (hbdd : BddAbove (N.oneShotEntanglementAssistedClassicalRateSet ε)) :
    lowerBound ≤ N.oneShotEntanglementAssistedClassicalCapacityFinite ε := by
  rw [N.oneShotEntanglementAssistedClassicalCapacityFinite_eq_sSup]
  exact W.lowerBound_le_rate.trans
    (le_csSup hbdd W.rate_mem_oneShotEntanglementAssistedClassicalRateSet)

end EntanglementAssistedOneShotAchievabilityWitness

end

end QIT
