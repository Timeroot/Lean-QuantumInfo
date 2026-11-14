/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Security.RandomnessExtraction
public import QIT.OneShot.SmoothEndpoint
public import QIT.Information.Entropy.Log2Lemmas

/-!
# Optimized conditional-min-entropy extractor bound

This module adds the slack step from feasible conditional-min-entropy
candidates to the optimized `State.conditionalMinEntropy` value.  The slack is
kept explicit, so no theorem asserts that the supremum defining the entropy is
attained.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe uF uZ uS ue

noncomputable section

namespace State

variable {a : Type uZ} {b : Type ue}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

/-- A full-rank perturbation of a side-information state. -/
def fullRankPerturb [Nonempty b] (σ : State b) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : State b where
  matrix := t • σ.matrix + (1 - t) • (maximallyMixed b).matrix
  pos := by
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul σ.pos ht0)
      (Matrix.PosSemidef.smul (maximallyMixed b).pos (sub_nonneg.mpr ht1))
  trace_eq_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      σ.trace_eq_one, (maximallyMixed b).trace_eq_one]
    norm_num

@[simp]
theorem fullRankPerturb_matrix [Nonempty b] (σ : State b) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (fullRankPerturb σ t ht0 ht1).matrix =
      t • σ.matrix + (1 - t) • (maximallyMixed b).matrix :=
  rfl

/-- A nontrivial full-rank perturbation is positive definite. -/
theorem fullRankPerturb_posDef [Nonempty b] (σ : State b) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ht_lt : t < 1) :
    (fullRankPerturb σ t ht0 ht1).matrix.PosDef := by
  have hσ :
      (t • σ.matrix).PosSemidef :=
    Matrix.PosSemidef.smul σ.pos ht0
  have hmm :
      ((1 - t) • (maximallyMixed b).matrix).PosDef :=
    Matrix.PosDef.smul (maximallyMixed_posDef (a := b)) (sub_pos.mpr ht_lt)
  simpa [fullRankPerturb] using Matrix.PosDef.posSemidef_add hσ hmm

private theorem rpow_two_neg_sub_mul_rpow_two_neg (lam η : ℝ) :
    Real.rpow 2 (-(lam - η)) * Real.rpow 2 (-η) = Real.rpow 2 (-lam) := by
  calc
    Real.rpow 2 (-(lam - η)) * Real.rpow 2 (-η) =
        Real.rpow 2 (-(lam - η) + -η) := by
          exact (Real.rpow_add (by norm_num : (0 : ℝ) < 2) (-(lam - η)) (-η)).symm
    _ = Real.rpow 2 (-lam) := by
          rw [show -(lam - η) + -η = -lam by ring]

/--
Any normalized conditional-min feasible witness can be made positive definite
after losing an arbitrary positive exponent slack.
-/
theorem ConditionalMinEntropyFeasible.exists_posDef_of_sub_slack
    [Nonempty b] {ρ : State (Prod a b)} {σ : State b} {lam η : ℝ}
    (hη : 0 < η)
    (hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    ∃ τ : State b,
      τ.matrix.PosDef ∧ ConditionalMinEntropyFeasible (a := a) ρ τ (lam - η) := by
  let t : ℝ := Real.rpow 2 (-η)
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-η)).le
  have ht_lt : t < 1 := by
    have hpow_gt : 1 < Real.rpow 2 η := by
      simpa using Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hη
    calc
      t = (Real.rpow 2 η)⁻¹ := by
            dsimp [t]
            rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      _ < 1 := inv_lt_one_of_one_lt₀ hpow_gt
  have ht1 : t ≤ 1 := le_of_lt ht_lt
  let τ : State b := fullRankPerturb σ t ht0 ht1
  refine ⟨τ, fullRankPerturb_posDef σ ht0 ht1 ht_lt, ?_⟩
  rw [ConditionalMinEntropyFeasible] at hfeas ⊢
  let cMu : ℝ := Real.rpow 2 (-(lam - η))
  let cLam : ℝ := Real.rpow 2 (-lam)
  have hmul : cMu * t = cLam := by
    dsimp [cMu, cLam, t]
    exact rpow_two_neg_sub_mul_rpow_two_neg lam η
  have hmulC : (t : ℂ) * (cMu : ℂ) = (cLam : ℂ) := by
    exact_mod_cast (by simpa [mul_comm] using hmul)
  have hside :
      (cMu : ℂ) • identityTensorStateMatrix (a := a) τ =
        (cLam : ℂ) • identityTensorStateMatrix (a := a) σ +
          ((cMu * (1 - t) : ℝ) : ℂ) •
            identityTensorStateMatrix (a := a) (maximallyMixed b) := by
    ext x y
    by_cases hxy : x.1 = y.1
    · simp [τ, fullRankPerturb, identityTensorStateMatrix, Matrix.kronecker,
        Matrix.kroneckerMap_apply, Matrix.one_apply, hxy, mul_add,
        mul_assoc, mul_left_comm, mul_comm]
      rw [← mul_assoc, hmulC]
    · simp [τ, fullRankPerturb, identityTensorStateMatrix, Matrix.kronecker,
        Matrix.kroneckerMap_apply, Matrix.one_apply, hxy]
  have hterm_psd :
      (((cMu * (1 - t) : ℝ) : ℂ) •
          identityTensorStateMatrix (a := a) (maximallyMixed b)).PosSemidef := by
    have hcMu : 0 ≤ cMu := by
      dsimp [cMu]
      exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(lam - η))
    have hcoeff : (0 : ℂ) ≤ (((cMu * (1 - t) : ℝ) : ℂ)) := by
      exact_mod_cast mul_nonneg hcMu (sub_nonneg.mpr ht1)
    exact Matrix.PosSemidef.smul
      (identityTensorStateMatrix_posSemidef (a := a) (maximallyMixed b)) hcoeff
  have hterm_nonneg :
      (0 : CMatrix (Prod a b)) ≤
        ((cMu * (1 - t) : ℝ) : ℂ) •
          identityTensorStateMatrix (a := a) (maximallyMixed b) := by
    simpa [Matrix.le_iff] using hterm_psd
  rw [hside]
  exact le_trans hfeas (le_add_of_nonneg_right hterm_nonneg)

end State

namespace Security

variable {F : Type uF} {Z : Type uZ} {S : Type uS} {e : Type ue}
variable [Fintype F] [DecidableEq F] [Nonempty F]
variable [Fintype Z] [DecidableEq Z]
variable [Fintype S] [DecidableEq S] [Nonempty S]
variable [Fintype e] [DecidableEq e]

private theorem rpow_two_two_mul_log2_pos {x : ℝ} (hx : 0 < x) :
    Real.rpow 2 (2 * log2 x) = x ^ 2 := by
  calc
    Real.rpow 2 (2 * log2 x) =
        Real.rpow 2 (log2 x * (2 : ℝ)) := by ring_nf
    _ = (Real.rpow 2 (log2 x)) ^ (2 : ℝ) := by
          exact Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (log2 x) (2 : ℝ)
    _ = x ^ (2 : ℝ) := by rw [rpow_two_log2_pos hx]
    _ = x ^ 2 := by exact Real.rpow_two x

private theorem rpow_two_log2_sub_eq_mul_rpow_neg {x h : ℝ} (hx : 0 < x) :
    Real.rpow 2 (log2 x - h) = x * Real.rpow 2 (-h) := by
  calc
    Real.rpow 2 (log2 x - h) =
        Real.rpow 2 (log2 x + -h) := by ring_nf
    _ = Real.rpow 2 (log2 x) * Real.rpow 2 (-h) := by
          exact Real.rpow_add (by norm_num : (0 : ℝ) < 2) (log2 x) (-h)
    _ = x * Real.rpow 2 (-h) := by rw [rpow_two_log2_pos hx]

private theorem rpow_two_neg_two_mul_log2_one_div_pos {ε : ℝ} (hε : 0 < ε) :
    Real.rpow 2 (-2 * log2 (1 / ε)) = ε ^ 2 := by
  calc
    Real.rpow 2 (-2 * log2 (1 / ε)) =
        Real.rpow 2 (2 * log2 ε) := by
          rw [log2_one_div]
          ring_nf
    _ = ε ^ 2 := rpow_two_two_mul_log2_pos hε

/--
The source-form output-length condition implies the square-root secrecy
condition used by the direct leftover-hash extractor bound.
-/
private theorem sqrt_mul_rpow_two_neg_le_of_log2_le_sub_two_log2_one_div
    {x ε h : ℝ} (hx : 0 < x) (hε : 0 < ε)
    (hlog : log2 x ≤ h - 2 * log2 (1 / ε)) :
    Real.sqrt (x * Real.rpow 2 (-h)) ≤ ε := by
  have hexponent : log2 x - h ≤ -2 * log2 (1 / ε) := by
    linarith
  have hpow :
      Real.rpow 2 (log2 x - h) ≤
        Real.rpow 2 (-2 * log2 (1 / ε)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexponent
  rw [rpow_two_log2_sub_eq_mul_rpow_neg hx,
    rpow_two_neg_two_mul_log2_one_div_pos hε] at hpow
  have hsqrt :
      Real.sqrt (x * Real.rpow 2 (-h)) ≤ Real.sqrt (ε ^ 2) :=
    Real.sqrt_le_sqrt hpow
  have hsqrt_eps : Real.sqrt (ε ^ 2) = ε := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hε]
  simpa [hsqrt_eps] using hsqrt

namespace HashFamily

omit [Nonempty F] in
/--
Optimized direct leftover-hash secrecy-distance bound with explicit slack.

For every `η > 0`, the direct fixed-witness bound can be applied to a
positive-definite feasible exponent below `H_min(Z|E)`, then weakened to the
source-shaped exponent `H_min(Z|E) - η`.  No supremum-attainment statement is
used or asserted.
-/
theorem extractorSecrecyDistance_le_sqrt_card_mul_rpow_of_collisionUniform_conditionalMinEntropy_sub_slack
    (H : HashFamily F Z S) (hH : H.CollisionUniform)
    (E : Ensemble Z e) {η : ℝ} (hη : 0 < η) :
    extractorSecrecyDistance (extractorOutputState H E) ≤
      Real.sqrt
        ((Fintype.card S : ℝ) *
          Real.rpow 2 (-(E.cqState.conditionalMinEntropy - η))) := by
  classical
  have hprod : Nonempty (Prod Z e) := E.cqState.nonempty
  letI : Nonempty (Prod Z e) := hprod
  let prodWitness : Prod Z e := Classical.choice hprod
  letI : Nonempty Z := ⟨prodWitness.1⟩
  letI : Nonempty e := ⟨prodWitness.2⟩
  let δ : ℝ := η / 2
  have hδ_pos : 0 < δ := by positivity
  let s : Set ℝ := E.cqState.conditionalMinEntropyFeasibleExponentValueSet (a := Z)
  have hs_nonempty : s.Nonempty := by
    simpa [s] using
      E.cqState.conditionalMinEntropyFeasibleExponentValueSet_nonempty (a := Z)
  have hs_eq :
      E.cqState.conditionalMinEntropy = sSup s := by
    simp [s, State.conditionalMinEntropy_eq,
      State.conditionalMinEntropyFeasibleExponentValueSet]
  have hlt_sup :
      E.cqState.conditionalMinEntropy - δ < sSup s := by
    rw [← hs_eq]
    exact sub_lt_self _ hδ_pos
  rcases exists_lt_of_lt_csSup hs_nonempty hlt_sup with
    ⟨lam, hlam_mem, hlt_lam⟩
  rcases hlam_mem with ⟨σ, hσfeas⟩
  rcases State.ConditionalMinEntropyFeasible.exists_posDef_of_sub_slack
      (a := Z) (b := e) (η := δ) hδ_pos hσfeas with
    ⟨τ, hτ_pos, hτ_feas⟩
  have hbase :
      extractorSecrecyDistance (extractorOutputState H E) ≤
        Real.sqrt ((Fintype.card S : ℝ) * Real.rpow 2 (-(lam - δ))) :=
    H.extractorSecrecyDistance_le_sqrt_card_mul_rpow_of_collisionUniform_conditionalMinEntropyFeasible_posDef
      hH E τ (lam - δ) hτ_pos hτ_feas
  have hmu_ge : E.cqState.conditionalMinEntropy - η ≤ lam - δ := by
    dsimp [δ] at hlt_lam ⊢
    linarith
  have hexp_le :
      Real.rpow 2 (-(lam - δ)) ≤
        Real.rpow 2 (-(E.cqState.conditionalMinEntropy - η)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
    linarith
  have hcard_nonneg : 0 ≤ (Fintype.card S : ℝ) := by positivity
  exact hbase.trans
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hexp_le hcard_nonneg))

omit [DecidableEq S] [Nonempty S] in
/-- Right-continuity at zero of the direct leftover-hash bound's slack factor. -/
private theorem extractorSecrecyDistance_conditionalMinEntropy_slack_rhs_tendsto
    (E : Ensemble Z e) :
    Filter.Tendsto
      (fun η : ℝ =>
        Real.sqrt
          ((Fintype.card S : ℝ) *
            Real.rpow 2 (-(E.cqState.conditionalMinEntropy - η))))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (Real.sqrt
          ((Fintype.card S : ℝ) *
            Real.rpow 2 (-(E.cqState.conditionalMinEntropy)))) ) := by
  have hexponent : Continuous
      (fun η : ℝ => -(E.cqState.conditionalMinEntropy - η)) := by
    fun_prop
  have hrpow : Continuous
      (fun η : ℝ => Real.rpow 2 (-(E.cqState.conditionalMinEntropy - η))) :=
    (Real.continuous_const_rpow (a := (2 : ℝ)) (by norm_num)).comp hexponent
  have hcont : Continuous
      (fun η : ℝ =>
        Real.sqrt
          ((Fintype.card S : ℝ) *
            Real.rpow 2 (-(E.cqState.conditionalMinEntropy - η))))
      :=
    Real.continuous_sqrt.comp (continuous_const.mul hrpow)
  have hcont0 : ContinuousAt
      (fun η : ℝ =>
        Real.sqrt
          ((Fintype.card S : ℝ) *
            Real.rpow 2 (-(E.cqState.conditionalMinEntropy - η))))
      0 :=
    hcont.continuousAt
  simpa using hcont0.tendsto.mono_left nhdsWithin_le_nhds

omit [Nonempty F] in
/--
Optimized direct leftover-hash secrecy-distance bound in source form.

The proof closes the explicit-slack theorem by taking `η → 0+`; it does not
assert that the supremum defining conditional min-entropy is attained.
-/
theorem extractorSecrecyDistance_le_sqrt_card_mul_rpow_of_collisionUniform_conditionalMinEntropy
    (H : HashFamily F Z S) (hH : H.CollisionUniform)
    (E : Ensemble Z e) :
    extractorSecrecyDistance (extractorOutputState H E) ≤
      Real.sqrt
        ((Fintype.card S : ℝ) *
          Real.rpow 2 (-(E.cqState.conditionalMinEntropy))) := by
  exact ge_of_tendsto
    (extractorSecrecyDistance_conditionalMinEntropy_slack_rhs_tendsto
      (S := S) E)
    (by
      filter_upwards [self_mem_nhdsWithin] with η hη
      exact
        H.extractorSecrecyDistance_le_sqrt_card_mul_rpow_of_collisionUniform_conditionalMinEntropy_sub_slack
          hH E hη)

omit [Nonempty F] in
/--
Smooth direct extractor secrecy from a cq-restricted smooth min-entropy
candidate.

The cq witness supplies a nearby ensemble `E'`.  The unsmoothed direct theorem
is applied to `E'`, then the purified-distance stability bridge transfers the
secrecy guarantee back to `E`.
-/
theorem isEpsilonSecretExtractor_of_collisionUniform_cqSmoothConditionalMinEntropyCandidate_le
    (H : HashFamily F Z S) (hH : H.CollisionUniform)
    (E : Ensemble Z e) {ε₁ ε₂ h : ℝ}
    (hcq : E.CqSmoothConditionalMinEntropyCandidate ε₁ h)
    (hε :
      Real.sqrt ((Fintype.card S : ℝ) * Real.rpow 2 (-h)) ≤ ε₂) :
    H.IsEpsilonSecretExtractor (2 * ε₁ + ε₂) E := by
  rcases hcq with ⟨E', hball, hmin_le⟩
  have hbound :
      Real.sqrt
        ((Fintype.card S : ℝ) *
          Real.rpow 2 (-(E'.cqState.conditionalMinEntropy))) ≤ ε₂ := by
    have hexp_le :
        Real.rpow 2 (-(E'.cqState.conditionalMinEntropy)) ≤
          Real.rpow 2 (-h) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
      linarith
    have hcard_nonneg : 0 ≤ (Fintype.card S : ℝ) := by positivity
    exact
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hexp_le hcard_nonneg)).trans hε
  have hsecret : H.IsEpsilonSecretExtractor ε₂ E' :=
    (H.extractorSecrecyDistance_le_sqrt_card_mul_rpow_of_collisionUniform_conditionalMinEntropy
      hH E').trans hbound
  exact H.isEpsilonSecretExtractor_of_purifiedBall_cqState E E' hball hsecret

/--
The direct source-form leftover-hash bound witnesses achievability of the
hash family's output length.
-/
theorem outputLengthAchievable_of_collisionUniform_conditionalMinEntropy_le
    (H : HashFamily F Z S) (hH : H.CollisionUniform)
    (E : Ensemble Z e) {ε : ℝ}
    (hε :
      Real.sqrt
        ((Fintype.card S : ℝ) *
          Real.rpow 2 (-(E.cqState.conditionalMinEntropy))) ≤ ε) :
    ExtractorOutputLengthAchievable.{uF, uZ, uS, ue}
      E ε H.outputLength := by
  have hsecret : H.IsEpsilonSecretExtractor ε E :=
    (H.extractorSecrecyDistance_le_sqrt_card_mul_rpow_of_collisionUniform_conditionalMinEntropy
      hH E).trans hε
  exact H.outputLengthAchievable E hsecret

/--
A cq-restricted smooth min-entropy candidate witnesses achievability of the hash
family's output length with the expected `2ε₁ + ε₂` smoothing/stability loss.
-/
theorem outputLengthAchievable_of_collisionUniform_cqSmoothConditionalMinEntropyCandidate_le
    (H : HashFamily F Z S) (hH : H.CollisionUniform)
    (E : Ensemble Z e) {ε₁ ε₂ h : ℝ}
    (hcq : E.CqSmoothConditionalMinEntropyCandidate ε₁ h)
    (hε :
      Real.sqrt ((Fintype.card S : ℝ) * Real.rpow 2 (-h)) ≤ ε₂) :
    ExtractorOutputLengthAchievable.{uF, uZ, uS, ue}
      E (2 * ε₁ + ε₂) H.outputLength := by
  exact H.outputLengthAchievable E
    (H.isEpsilonSecretExtractor_of_collisionUniform_cqSmoothConditionalMinEntropyCandidate_le
      hH E hcq hε)

/--
The direct source-form leftover-hash bound contributes the concrete
`log₂ |S|` value to the extractable-randomness value set.
-/
theorem extractableRandomnessLogValue_mem_of_collisionUniform_conditionalMinEntropy_le
    (H : HashFamily F Z S) (hH : H.CollisionUniform)
    (E : Ensemble Z e) {ε : ℝ}
    (hε :
      Real.sqrt
        ((Fintype.card S : ℝ) *
          Real.rpow 2 (-(E.cqState.conditionalMinEntropy))) ≤ ε) :
    log2 (H.outputLength : ℝ) ∈
      ExtractableRandomnessLogValueSet.{uF, uZ, uS, ue} E ε := by
  have hsecret : H.IsEpsilonSecretExtractor ε E :=
    (H.extractorSecrecyDistance_le_sqrt_card_mul_rpow_of_collisionUniform_conditionalMinEntropy
      hH E).trans hε
  exact H.extractableRandomnessLogValue_mem E hsecret

/--
A cq-restricted smooth min-entropy candidate contributes `log₂ |S|` to the
extractable-randomness value set after the `2ε₁ + ε₂` stability loss.
-/
theorem extractableRandomnessLogValue_mem_of_collisionUniform_cqSmoothConditionalMinEntropyCandidate_le
    (H : HashFamily F Z S) (hH : H.CollisionUniform)
    (E : Ensemble Z e) {ε₁ ε₂ h : ℝ}
    (hcq : E.CqSmoothConditionalMinEntropyCandidate ε₁ h)
    (hε :
      Real.sqrt ((Fintype.card S : ℝ) * Real.rpow 2 (-h)) ≤ ε₂) :
    log2 (H.outputLength : ℝ) ∈
      ExtractableRandomnessLogValueSet.{uF, uZ, uS, ue} E (2 * ε₁ + ε₂) := by
  exact H.extractableRandomnessLogValue_mem E
    (H.isEpsilonSecretExtractor_of_collisionUniform_cqSmoothConditionalMinEntropyCandidate_le
      hH E hcq hε)

end HashFamily

omit [Fintype F] [DecidableEq F] [Nonempty F] [Fintype S] [DecidableEq S]
    [Nonempty S] in
/--
The full-function `Fin ell` family witnesses direct achievability for every
positive concrete output length satisfying the unsmoothed source-form bound.
-/
theorem finFullFunctionHashFamily_outputLengthAchievable_of_conditionalMinEntropy_le
    {ell : Nat} (hell : 0 < ell) (E : Ensemble Z e) {ε : ℝ}
    (hε :
      Real.sqrt
        ((ell : ℝ) *
          Real.rpow 2 (-(E.cqState.conditionalMinEntropy))) ≤ ε) :
    ExtractorOutputLengthAchievable.{uZ, uZ, 0, ue} E ε ell := by
  letI : Nonempty (Fin ell) := ⟨⟨0, hell⟩⟩
  let H := FinFullFunctionHashFamily (Z := Z) ell hell
  have hεH :
      Real.sqrt
        ((Fintype.card (Fin ell) : ℝ) *
          Real.rpow 2 (-(E.cqState.conditionalMinEntropy))) ≤ ε := by
    simpa using hε
  have hAch :
      ExtractorOutputLengthAchievable.{uZ, uZ, 0, ue} E ε H.outputLength :=
    H.outputLengthAchievable_of_collisionUniform_conditionalMinEntropy_le
      (finFullFunctionHashFamily_collisionUniform (Z := Z) hell) E hεH
  simpa [H, finFullFunctionHashFamily_outputLength (Z := Z) hell] using hAch

omit [Fintype F] [DecidableEq F] [Nonempty F] [Fintype S] [DecidableEq S]
    [Nonempty S] in
/--
The full-function `Fin ell` family witnesses direct achievability from a
cq-restricted smooth min-entropy candidate.
-/
theorem finFullFunctionHashFamily_outputLengthAchievable_of_cqSmoothConditionalMinEntropyCandidate_le
    {ell : Nat} (hell : 0 < ell) (E : Ensemble Z e) {ε₁ ε₂ h : ℝ}
    (hcq : E.CqSmoothConditionalMinEntropyCandidate ε₁ h)
    (hε :
      Real.sqrt ((ell : ℝ) * Real.rpow 2 (-h)) ≤ ε₂) :
    ExtractorOutputLengthAchievable.{uZ, uZ, 0, ue}
      E (2 * ε₁ + ε₂) ell := by
  letI : Nonempty (Fin ell) := ⟨⟨0, hell⟩⟩
  let H := FinFullFunctionHashFamily (Z := Z) ell hell
  have hεH :
      Real.sqrt
        ((Fintype.card (Fin ell) : ℝ) *
          Real.rpow 2 (-h)) ≤ ε₂ := by
    simpa using hε
  have hAch :
      ExtractorOutputLengthAchievable.{uZ, uZ, 0, ue}
        E (2 * ε₁ + ε₂) H.outputLength :=
    H.outputLengthAchievable_of_collisionUniform_cqSmoothConditionalMinEntropyCandidate_le
      (finFullFunctionHashFamily_collisionUniform (Z := Z) hell) E hcq hεH
  simpa [H, finFullFunctionHashFamily_outputLength (Z := Z) hell] using hAch

omit [Fintype F] [DecidableEq F] [Nonempty F] [Fintype S] [DecidableEq S]
    [Nonempty S] in
/--
The full-function `Fin ell` family contributes `log₂ ell` to the direct
extractable-randomness value set under the unsmoothed source-form bound.
-/
theorem finFullFunctionHashFamily_extractableRandomnessLogValue_mem_of_conditionalMinEntropy_le
    {ell : Nat} (hell : 0 < ell) (E : Ensemble Z e) {ε : ℝ}
    (hε :
      Real.sqrt
        ((ell : ℝ) *
          Real.rpow 2 (-(E.cqState.conditionalMinEntropy))) ≤ ε) :
    log2 (ell : ℝ) ∈
      ExtractableRandomnessLogValueSet.{uZ, uZ, 0, ue} E ε := by
  letI : Nonempty (Fin ell) := ⟨⟨0, hell⟩⟩
  let H := FinFullFunctionHashFamily (Z := Z) ell hell
  have hεH :
      Real.sqrt
        ((Fintype.card (Fin ell) : ℝ) *
          Real.rpow 2 (-(E.cqState.conditionalMinEntropy))) ≤ ε := by
    simpa using hε
  have hMem :
      log2 (H.outputLength : ℝ) ∈
        ExtractableRandomnessLogValueSet.{uZ, uZ, 0, ue} E ε :=
    H.extractableRandomnessLogValue_mem_of_collisionUniform_conditionalMinEntropy_le
      (finFullFunctionHashFamily_collisionUniform (Z := Z) hell) E hεH
  simpa [H, finFullFunctionHashFamily_outputLength (Z := Z) hell] using hMem

omit [Fintype F] [DecidableEq F] [Nonempty F] [Fintype S] [DecidableEq S]
    [Nonempty S] in
/--
The full-function `Fin ell` family contributes `log₂ ell` to the smooth direct
value set from a cq-restricted smooth min-entropy candidate.
-/
theorem finFullFunctionHashFamily_extractableRandomnessLogValue_mem_of_cqSmoothConditionalMinEntropyCandidate_le
    {ell : Nat} (hell : 0 < ell) (E : Ensemble Z e) {ε₁ ε₂ h : ℝ}
    (hcq : E.CqSmoothConditionalMinEntropyCandidate ε₁ h)
    (hε :
      Real.sqrt ((ell : ℝ) * Real.rpow 2 (-h)) ≤ ε₂) :
    log2 (ell : ℝ) ∈
      ExtractableRandomnessLogValueSet.{uZ, uZ, 0, ue}
        E (2 * ε₁ + ε₂) := by
  letI : Nonempty (Fin ell) := ⟨⟨0, hell⟩⟩
  let H := FinFullFunctionHashFamily (Z := Z) ell hell
  have hεH :
      Real.sqrt
        ((Fintype.card (Fin ell) : ℝ) *
          Real.rpow 2 (-h)) ≤ ε₂ := by
    simpa using hε
  have hMem :
      log2 (H.outputLength : ℝ) ∈
        ExtractableRandomnessLogValueSet.{uZ, uZ, 0, ue}
          E (2 * ε₁ + ε₂) :=
    H.extractableRandomnessLogValue_mem_of_collisionUniform_cqSmoothConditionalMinEntropyCandidate_le
      (finFullFunctionHashFamily_collisionUniform (Z := Z) hell) E hcq hεH
  simpa [H, finFullFunctionHashFamily_outputLength (Z := Z) hell] using hMem

omit [Fintype F] [DecidableEq F] [Nonempty F] [Fintype S] [DecidableEq S]
    [Nonempty S] in
/--
The smooth direct source-form lower bound for every concrete positive output
length satisfying
`log₂ ell ≤ h - 2 log₂ (1 / ε₂)`.

The cq smooth min-entropy candidate supplies the `ε₁`-smooth entropy witness;
the purified-distance bridge contributes the expected `2ε₁` stability loss,
so the extractable-randomness value set is evaluated at `2ε₁ + ε₂`.
-/
theorem finFullFunctionHashFamily_extractableRandomnessLogValue_mem_of_cqSmoothConditionalMinEntropyCandidate_log_le
    {ell : Nat} (hell : 0 < ell) (E : Ensemble Z e) {ε₁ ε₂ h : ℝ}
    (hε₂ : 0 < ε₂)
    (hcq : E.CqSmoothConditionalMinEntropyCandidate ε₁ h)
    (hlog : log2 (ell : ℝ) ≤ h - 2 * log2 (1 / ε₂)) :
    log2 (ell : ℝ) ∈
      ExtractableRandomnessLogValueSet.{uZ, uZ, 0, ue}
        E (2 * ε₁ + ε₂) := by
  have hell_real : 0 < (ell : ℝ) := by exact_mod_cast hell
  have hε :
      Real.sqrt ((ell : ℝ) * Real.rpow 2 (-h)) ≤ ε₂ :=
    sqrt_mul_rpow_two_neg_le_of_log2_le_sub_two_log2_one_div
      hell_real hε₂ hlog
  exact
    finFullFunctionHashFamily_extractableRandomnessLogValue_mem_of_cqSmoothConditionalMinEntropyCandidate_le
      (Z := Z) hell E hcq hε

end Security

end

end QIT
