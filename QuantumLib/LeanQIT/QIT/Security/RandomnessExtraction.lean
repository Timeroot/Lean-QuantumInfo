/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Security.ExtractorQuadraticBridge

/-!
# Direct randomness-extraction bound

This module assembles the extractor trace bridge, centered collision-uniform
quadratic collapse, and positive-definite conditional-min-entropy quadratic
bound into the direct leftover-hash achievability statement.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT.Security

universe uF uZ uS ue

noncomputable section

variable {F : Type uF} {Z : Type uZ} {S : Type uS} {e : Type ue}
variable [Fintype F] [DecidableEq F] [Nonempty F]
variable [Fintype Z] [DecidableEq Z]
variable [Fintype S] [DecidableEq S] [Nonempty S]
variable [Fintype e] [DecidableEq e]

namespace HashFamily

/--
An `ε`-secret extractor is an extractor whose public-seed output state is within
secrecy distance `ε` of the ideal uniform output independent of the seed and
side information.

[Tomamichel2015FiniteResources, apps.tex:256-292]
-/
def IsEpsilonSecretExtractor (H : HashFamily F Z S) (ε : ℝ) (E : Ensemble Z e) :
    Prop :=
  extractorSecrecyDistance (extractorOutputState H E) ≤ ε

omit [Nonempty F] [DecidableEq Z] in
@[simp]
theorem isEpsilonSecretExtractor_iff
    (H : HashFamily F Z S) (ε : ℝ) (E : Ensemble Z e) :
    H.IsEpsilonSecretExtractor ε E ↔
      extractorSecrecyDistance (extractorOutputState H E) ≤ ε :=
  Iff.rfl

omit [Nonempty F] [DecidableEq Z] in
/--
Extractor-level stability wrapper for two nearby output/ideal pairs.

The two closeness hypotheses are intentionally explicit: later cq/channel
bridges can discharge them from a purified-distance ball between input cq
states without changing this secrecy-transfer theorem.
-/
theorem isEpsilonSecretExtractor_of_output_ideal_closeness
    (H : HashFamily F Z S) (E E' : Ensemble Z e) {δ ε : ℝ}
    (hstate :
      (extractorOutputState H E).normalizedTraceDistance
        (extractorOutputState H E') ≤ δ)
    (hideal :
      (idealExtractorOutputState (extractorOutputState H E')).normalizedTraceDistance
        (idealExtractorOutputState (extractorOutputState H E)) ≤ δ)
    (hsecret : H.IsEpsilonSecretExtractor ε E') :
    H.IsEpsilonSecretExtractor (2 * δ + ε) E :=
  extractorSecrecyDistance_le_two_mul_delta_add_of_ideal_closeness
    (extractorOutputState H E) (extractorOutputState H E') hstate hideal hsecret

omit [Nonempty F] [DecidableEq Z] in
/--
Extractor secrecy is stable under normalized trace distance between the full
public-seed extractor output states.  The ideal-output perturbation is handled
by the reusable idealization-channel contraction.
-/
theorem isEpsilonSecretExtractor_of_output_closeness
    (H : HashFamily F Z S) (E E' : Ensemble Z e) {δ ε : ℝ}
    (hstate :
      (extractorOutputState H E).normalizedTraceDistance
        (extractorOutputState H E') ≤ δ)
    (hsecret : H.IsEpsilonSecretExtractor ε E') :
    H.IsEpsilonSecretExtractor (2 * δ + ε) E :=
  extractorSecrecyDistance_le_two_mul_normalizedTraceDistance_add
    (extractorOutputState H E) (extractorOutputState H E') hstate hsecret

omit [Nonempty F] in
/--
Extractor secrecy transfers across a purified-distance ball between input cq
states.  Fuchs--van de Graaf converts the purified-distance premise to
normalized trace distance, and the extractor-output channel gives data
processing for the public-seed output.
-/
theorem isEpsilonSecretExtractor_of_purifiedBall_cqState
    (H : HashFamily F Z S) (E E' : Ensemble Z e) {ε₁ ε₂ : ℝ}
    (hball : E.cqState.purifiedBall ε₁ E'.cqState)
    (hsecret : H.IsEpsilonSecretExtractor ε₂ E') :
    H.IsEpsilonSecretExtractor (2 * ε₁ + ε₂) E := by
  have htrace :
      E.cqState.normalizedTraceDistance E'.cqState ≤
        E.cqState.purifiedDistance E'.cqState := by
    simpa [State.purifiedDistance_eq] using
      State.fuchs_van_de_graaf_upper E.cqState E'.cqState
  have hclose :
      (extractorOutputState H E).normalizedTraceDistance
          (extractorOutputState H E') ≤ ε₁ :=
    (H.extractorOutputState_normalizedTraceDistance_le_cqState E E').trans
      (htrace.trans hball)
  exact H.isEpsilonSecretExtractor_of_output_closeness E E' hclose hsecret

/-- The source output alphabet size `d_S` of a finite extractor. -/
def outputLength (_H : HashFamily F Z S) : Nat :=
  Fintype.card S

omit [DecidableEq F] [Nonempty F] [Fintype Z] [DecidableEq Z] [DecidableEq S] [Nonempty S] in
@[simp]
theorem outputLength_eq_card (H : HashFamily F Z S) :
    H.outputLength = Fintype.card S :=
  rfl

end HashFamily

/-- The full-function `Fin ell` specialization has output length `ell`. -/
theorem finFullFunctionHashFamily_outputLength
    {Z : Type uZ} [Fintype Z] [DecidableEq Z] {ell : Nat} (hell : 0 < ell) :
    (FinFullFunctionHashFamily (Z := Z) ell hell).outputLength = ell := by
  letI : Nonempty (Fin ell) := ⟨⟨0, hell⟩⟩
  simp [HashFamily.outputLength]

/--
An output length `ell` is achievable for `E` at secrecy error `ε` if there is
some finite nonempty output alphabet of size `ell`, a finite nonempty seed
alphabet, and a hash family whose extractor is `ε`-secret on `E`.

[Tomamichel2015FiniteResources, apps.tex:294-299]
-/
def ExtractorOutputLengthAchievable
    (E : Ensemble Z e) (ε : ℝ) (ell : Nat) : Prop :=
  ∃ (S : Type uS) (instS : Fintype S) (decS : DecidableEq S) (nonS : Nonempty S),
    letI : Fintype S := instS
    letI : DecidableEq S := decS
    letI : Nonempty S := nonS
    Fintype.card S = ell ∧
      ∃ (F : Type uF) (instF : Fintype F) (decF : DecidableEq F) (nonF : Nonempty F),
        letI : Fintype F := instF
        letI : DecidableEq F := decF
        letI : Nonempty F := nonF
        ∃ H : HashFamily F Z S, H.IsEpsilonSecretExtractor ε E

/-- The natural-valued output lengths achievable for source-shaped randomness
extraction at secrecy error `ε`.

[Tomamichel2015FiniteResources, apps.tex:294-299]
-/
def ExtractableRandomnessLengthSet
    (E : Ensemble Z e) (ε : ℝ) : Set Nat :=
  {ell | ExtractorOutputLengthAchievable.{uF, uZ, uS, ue} E ε ell}

/--
The real log-values of achievable output lengths for source-shaped randomness
extraction.  The value is `log₂ ell`, matching Tomamichel's
`log₂ ℓ^ε(Z|E)_ρ` convention.  The registered endpoint keeps this supremum
interface; `RandomnessExtractionConverse` proves the Nat-valued maximum
equivalence layer.

[Tomamichel2015FiniteResources, apps.tex:294-299]
-/
def ExtractableRandomnessLogValueSet
    (E : Ensemble Z e) (ε : ℝ) : Set ℝ :=
  {r | ∃ ell : Nat,
    ExtractorOutputLengthAchievable.{uF, uZ, uS, ue} E ε ell ∧ r = log2 (ell : ℝ)}

omit [DecidableEq Z] in
/-- An achievable output length is positive, because it is the cardinality of a
nonempty output alphabet. -/
theorem extractorOutputLengthAchievable_pos
    {E : Ensemble Z e} {ε : ℝ} {ell : Nat}
    (hach : ExtractorOutputLengthAchievable.{uF, uZ, uS, ue} E ε ell) :
    0 < ell := by
  rcases hach with
    ⟨S', instS, decS, nonS, hcard, F', instF, decF, nonF, H, hsecret⟩
  letI : Fintype S' := instS
  letI : DecidableEq S' := decS
  letI : Nonempty S' := nonS
  have hcard_pos : 0 < Fintype.card S' := Fintype.card_pos
  simpa [hcard] using hcard_pos

/--
Source-shaped extractable randomness as the supremum of achievable log-output
lengths.  Direct and converse theorems can bound this real quantity without
reproving the interface layer.

[Tomamichel2015FiniteResources, apps.tex:294-299]
-/
def extractableRandomnessLog (E : Ensemble Z e) (ε : ℝ) : ℝ :=
  sSup (ExtractableRandomnessLogValueSet.{uF, uZ, uS, ue} E ε)

namespace HashFamily

omit [DecidableEq Z] in
/-- A concrete `ε`-secret extractor witnesses achievability of its output length. -/
theorem outputLengthAchievable
    (H : HashFamily F Z S) (E : Ensemble Z e) {ε : ℝ}
    (hsecret : H.IsEpsilonSecretExtractor ε E) :
    ExtractorOutputLengthAchievable.{uF, uZ, uS, ue} E ε H.outputLength := by
  refine ⟨S, inferInstance, inferInstance, inferInstance, ?_⟩
  dsimp
  refine ⟨rfl, F, inferInstance, inferInstance, inferInstance, ?_⟩
  dsimp
  exact ⟨H, hsecret⟩

omit [DecidableEq Z] in
/-- A concrete `ε`-secret extractor contributes its `log₂ |S|` value. -/
theorem extractableRandomnessLogValue_mem
    (H : HashFamily F Z S) (E : Ensemble Z e) {ε : ℝ}
    (hsecret : H.IsEpsilonSecretExtractor ε E) :
    log2 (H.outputLength : ℝ) ∈
      ExtractableRandomnessLogValueSet.{uF, uZ, uS, ue} E ε := by
  exact ⟨H.outputLength, H.outputLengthAchievable E hsecret, rfl⟩

omit [DecidableEq F] [Nonempty F] in
/--
Seed-averaged direct extractor bound in squared form.

This is the direct achievability route under the source-shaped
collision-uniform hash-family hypothesis and an explicit positive-definite
side-information reference state.
-/
theorem extractorSeedAverageTraceDistance_sq_le_card_mul_rpow_of_collisionUniform_conditionalMinEntropyFeasible_posDef
    (H : HashFamily F Z S) (hH : H.CollisionUniform)
    (E : Ensemble Z e) (σ : State e) (lam : ℝ)
    (hσ : σ.matrix.PosDef)
    (hmin : State.ConditionalMinEntropyFeasible (a := Z) E.cqState σ lam) :
    (extractorSeedAverageTraceDistance H E) ^ 2 ≤
      (Fintype.card S : ℝ) * Real.rpow 2 (-lam) := by
  classical
  let q : F → ℝ := fun f => H.extractorSeedCenteredQuadraticTerm E σ f
  have hcard_nonneg : 0 ≤ (Fintype.card S : ℝ) := by positivity
  have hq : ∀ f, 0 ≤ q f := by
    intro f
    simpa [q] using H.extractorSeedCenteredQuadraticTerm_nonneg_of_posDef E σ f hσ
  have hseed : ∀ f,
      extractorSeedTraceDistance H E f ≤
        Real.sqrt ((Fintype.card S : ℝ) * q f) := by
    intro f
    simpa [q] using
      H.extractorSeedTraceDistance_le_sqrt_card_mul_centeredQuadraticTerm_posDef
        E σ f hσ
  have havg :
      (extractorSeedAverageTraceDistance H E) ^ 2 ≤
        (Fintype.card S : ℝ) * extractorSeedQuadraticAverage H q :=
    H.extractorSeedAverageTraceDistance_sq_le_scaled_quadraticAverage
      E (Fintype.card S : ℝ) q hcard_nonneg hq hseed
  have hcollapse :
      extractorSeedQuadraticAverage H q ≤ extractorCqQuadraticTerm E σ := by
    simpa [q] using
      H.extractorSeedCenteredQuadraticAverage_le_cqQuadratic_of_collisionUniform_posDef
        E σ hH hσ
  have hcq :
      extractorCqQuadraticTerm E σ ≤ Real.rpow 2 (-lam) :=
    extractorCqQuadratic_le_rpow_of_conditionalMinEntropyFeasible_posDef
      E σ lam hσ hmin
  exact havg.trans
    (mul_le_mul_of_nonneg_left (hcollapse.trans hcq) hcard_nonneg)

omit [DecidableEq F] [Nonempty F] in
/--
Seed-averaged direct extractor bound from a positive-definite conditional
min-entropy candidate.

This wrapper exposes the optimized-entropy proof route without asserting that
the supremum in `State.conditionalMinEntropy` is attained.
-/
theorem extractorSeedAverageTraceDistance_sq_le_card_mul_rpow_of_collisionUniform_conditionalMinEntropyCandidate_posDef
    (H : HashFamily F Z S) (hH : H.CollisionUniform)
    (E : Ensemble Z e) (lam : ℝ)
    (hwit : ∃ σ : State e,
      σ.matrix.PosDef ∧ State.ConditionalMinEntropyFeasible (a := Z) E.cqState σ lam) :
    (extractorSeedAverageTraceDistance H E) ^ 2 ≤
      (Fintype.card S : ℝ) * Real.rpow 2 (-lam) := by
  rcases hwit with ⟨σ, hσ, hmin⟩
  exact
    H.extractorSeedAverageTraceDistance_sq_le_card_mul_rpow_of_collisionUniform_conditionalMinEntropyFeasible_posDef
      hH E σ lam hσ hmin

omit [Nonempty F] in
/--
Direct leftover-hash achievability bound for extractor secrecy distance.

The theorem proves the direct bound only, under `CollisionUniform` and
`σ.matrix.PosDef`; Tomamichel's converse and the full two-sided extractable
length theorem are intentionally outside this statement.
-/
theorem extractorSecrecyDistance_le_sqrt_card_mul_rpow_of_collisionUniform_conditionalMinEntropyFeasible_posDef
    (H : HashFamily F Z S) (hH : H.CollisionUniform)
    (E : Ensemble Z e) (σ : State e) (lam : ℝ)
    (hσ : σ.matrix.PosDef)
    (hmin : State.ConditionalMinEntropyFeasible (a := Z) E.cqState σ lam) :
    extractorSecrecyDistance (extractorOutputState H E) ≤
      Real.sqrt ((Fintype.card S : ℝ) * Real.rpow 2 (-lam)) := by
  classical
  let q : F → ℝ := fun f => H.extractorSeedCenteredQuadraticTerm E σ f
  have hcard_nonneg : 0 ≤ (Fintype.card S : ℝ) := by positivity
  have hq : ∀ f, 0 ≤ q f := by
    intro f
    simpa [q] using H.extractorSeedCenteredQuadraticTerm_nonneg_of_posDef E σ f hσ
  have hseed : ∀ f,
      extractorSeedTraceDistance H E f ≤
        Real.sqrt ((Fintype.card S : ℝ) * q f) := by
    intro f
    simpa [q] using
      H.extractorSeedTraceDistance_le_sqrt_card_mul_centeredQuadraticTerm_posDef
        E σ f hσ
  have hsec_sq_base :
      (extractorSecrecyDistance (extractorOutputState H E)) ^ 2 ≤
        (Fintype.card S : ℝ) * extractorSeedQuadraticAverage H q :=
    H.extractorSecrecyDistance_sq_le_scaled_quadraticAverage
      E (Fintype.card S : ℝ) q hcard_nonneg hq hseed
  have hcollapse :
      extractorSeedQuadraticAverage H q ≤ extractorCqQuadraticTerm E σ := by
    simpa [q] using
      H.extractorSeedCenteredQuadraticAverage_le_cqQuadratic_of_collisionUniform_posDef
        E σ hH hσ
  have hcq :
      extractorCqQuadraticTerm E σ ≤ Real.rpow 2 (-lam) :=
    extractorCqQuadratic_le_rpow_of_conditionalMinEntropyFeasible_posDef
      E σ lam hσ hmin
  have hsec_sq :
      (extractorSecrecyDistance (extractorOutputState H E)) ^ 2 ≤
        (Fintype.card S : ℝ) * Real.rpow 2 (-lam) :=
    hsec_sq_base.trans
      (mul_le_mul_of_nonneg_left (hcollapse.trans hcq) hcard_nonneg)
  exact Real.le_sqrt_of_sq_le hsec_sq

omit [Nonempty F] in
/--
Direct leftover-hash secrecy-distance bound from a positive-definite
conditional min-entropy candidate.

This is the source-shaped candidate bridge: a feasible witness `σ` for `lam`
feeds the existing fixed-witness extractor proof.  It intentionally keeps the
optimization step explicit instead of silently replacing `lam` by
`State.conditionalMinEntropy`.
-/
theorem extractorSecrecyDistance_le_sqrt_card_mul_rpow_of_collisionUniform_conditionalMinEntropyCandidate_posDef
    (H : HashFamily F Z S) (hH : H.CollisionUniform)
    (E : Ensemble Z e) (lam : ℝ)
    (hwit : ∃ σ : State e,
      σ.matrix.PosDef ∧ State.ConditionalMinEntropyFeasible (a := Z) E.cqState σ lam) :
    extractorSecrecyDistance (extractorOutputState H E) ≤
      Real.sqrt ((Fintype.card S : ℝ) * Real.rpow 2 (-lam)) := by
  rcases hwit with ⟨σ, hσ, hmin⟩
  exact
    H.extractorSecrecyDistance_le_sqrt_card_mul_rpow_of_collisionUniform_conditionalMinEntropyFeasible_posDef
      hH E σ lam hσ hmin

end HashFamily

/-- The one-seed, one-output hash family.  It witnesses that the extractable
randomness value set is nonempty for every nonnegative secrecy parameter. -/
def trivialHashFamily (Z : Type uZ) [Fintype Z] : HashFamily PUnit Z PUnit where
  hash := fun _ _ => PUnit.unit
  prob := fun _ => 1
  prob_sum := by simp

omit [DecidableEq Z] in
/-- The trivial extractor output is already ideal, since the output alphabet is
the singleton alphabet. -/
theorem trivialHashFamily_outputState_eq_ideal (E : Ensemble Z e) :
    extractorOutputState (trivialHashFamily Z) E =
      idealExtractorOutputState (extractorOutputState (trivialHashFamily Z) E) := by
  ext x y
  simp [trivialHashFamily, extractorOutputState, idealExtractorOutputState,
    extractorOutputMatrix, State.prod, State.marginalB,
    partialTraceA, uniformExtractorOutputState, uniformExtractorOutputProb]

omit [DecidableEq Z] in
/-- The trivial extractor has zero secrecy distance. -/
theorem trivialHashFamily_extractorSecrecyDistance_eq_zero (E : Ensemble Z e) :
    extractorSecrecyDistance (extractorOutputState (trivialHashFamily Z) E) = 0 := by
  let ρ : State (PUnit × (PUnit × e)) := extractorOutputState (trivialHashFamily Z) E
  have hstate : ρ = idealExtractorOutputState ρ := by
    dsimp [ρ]
    exact trivialHashFamily_outputState_eq_ideal E
  calc
    extractorSecrecyDistance (extractorOutputState (trivialHashFamily Z) E) =
        ρ.normalizedTraceDistance (idealExtractorOutputState ρ) := by rfl
    _ = ρ.normalizedTraceDistance ρ := by rw [← hstate]
    _ = 0 := State.normalizedTraceDistance_self ρ

omit [DecidableEq Z] in
/-- The trivial extractor is `ε`-secret for every nonnegative `ε`. -/
theorem trivialHashFamily_isEpsilonSecretExtractor
    (E : Ensemble Z e) {ε : ℝ} (hε : 0 ≤ ε) :
    (trivialHashFamily Z).IsEpsilonSecretExtractor ε E := by
  rw [HashFamily.isEpsilonSecretExtractor_iff]
  rw [trivialHashFamily_extractorSecrecyDistance_eq_zero]
  exact hε

omit [DecidableEq Z] in
/-- The one-output trivial extractor is always achievable for nonnegative
secrecy error. -/
theorem extractorOutputLengthAchievable_one_of_nonneg
    (E : Ensemble Z e) {ε : ℝ} (hε : 0 ≤ ε) :
    ExtractorOutputLengthAchievable.{uF, uZ, uS, ue} E ε 1 := by
  refine ⟨PUnit, inferInstance, inferInstance, inferInstance, ?_⟩
  dsimp
  refine ⟨by simp, PUnit, inferInstance, inferInstance, inferInstance, ?_⟩
  dsimp
  exact ⟨trivialHashFamily Z, trivialHashFamily_isEpsilonSecretExtractor E hε⟩

omit [DecidableEq Z] in
/-- The achievable output-length set is nonempty for every nonnegative secrecy
parameter. -/
theorem extractableRandomnessLengthSet_nonempty_of_nonneg
    (E : Ensemble Z e) {ε : ℝ} (hε : 0 ≤ ε) :
    (ExtractableRandomnessLengthSet.{uF, uZ, uS, ue} E ε).Nonempty := by
  exact ⟨1, extractorOutputLengthAchievable_one_of_nonneg E hε⟩

omit [DecidableEq Z] in
/-- Achievable extractable-randomness log values are nonempty for every
nonnegative secrecy parameter. -/
theorem extractableRandomnessLogValueSet_nonempty_of_nonneg
    (E : Ensemble Z e) {ε : ℝ} (hε : 0 ≤ ε) :
    (ExtractableRandomnessLogValueSet.{uF, uZ, uS, ue} E ε).Nonempty := by
  refine ⟨log2 ((1 : Nat) : ℝ), ?_⟩
  exact ⟨1, extractorOutputLengthAchievable_one_of_nonneg E hε, rfl⟩

end

end QIT.Security
