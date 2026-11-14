/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Asymptotic.Lower
public import QIT.Coding.EntanglementAssisted.Asymptotic.Upper.Assembly

/-!
# Asymptotic upper-bound public facade

This module is part of the entanglement-assisted classical communication
asymptotic proof spine.  It was split out mechanically from the historical
`EntanglementAssistedAsymptotic` files; theorem statements and proof routes are
unchanged.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Topology
open Filter

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace Channel

variable (N : Channel a b)

/-- The two finite-block, per-code upper bounds in the Khatri--Wilde
entanglement-assisted converse route.

The source displays the equivalent inequalities after division by the positive
blocklength.  These fields retain the log-cardinality form produced directly
by applying the proved one-shot bounds to the block channel `N.tensorPower n`.
-/
structure EntanglementAssistedFiniteBlockUpperBounds where
  weak_logCard_upper :
    ∀ (ε : ℝ), 0 ≤ ε → ε < 1 →
      ∀ (n : ℕ), 1 ≤ n →
        ∀ (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M],
          ∀ (EA : Type u) [Fintype EA] [DecidableEq EA],
            ∀ (EB : Type u) [Fintype EB] [DecidableEq EB],
              ∀ C : EntanglementAssistedClassicalCode N n M EA EB,
                C.maxErrorAtMost ε →
                  log2 (Fintype.card M : ℝ) ≤
                    (N.tensorPower n).entanglementAssistedWeakConverseBound ε
  sandwiched_logCard_upper :
    ∀ (ε α : ℝ), 0 ≤ ε → ε < 1 → 1 < α →
      ∀ (n : ℕ), 1 ≤ n →
        ∀ (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M],
          ∀ (EA : Type u) [Fintype EA] [DecidableEq EA],
            ∀ (EB : Type u) [Fintype EB] [DecidableEq EB],
              ∀ C : EntanglementAssistedClassicalCode N n M EA EB,
                C.maxErrorAtMost ε →
                  (log2 (Fintype.card M : ℝ) : EReal) ≤
                    (N.tensorPower n).sandwichedRenyiMutualInformationE α +
                      ((α / (α - 1) * log2 (1 / (1 - ε)) : ℝ) : EReal)

/-- Apply the one-shot weak and sandwiched-Renyi converse bounds to every
positive-length block channel. -/
theorem entanglementAssisted_finiteBlockUpperBounds
    [Nonempty a] :
    N.EntanglementAssistedFiniteBlockUpperBounds where
  weak_logCard_upper := by
    intro ε hε_nonneg hε_lt_one n _hn M _ _ _ EA _ _ EB _ _ C hC
    exact
      (C.asBlockOneShot).log_card_le_channel_entanglementAssistedWeakConverseBound
        hε_nonneg hε_lt_one (C.asBlockOneShot_maxErrorAtMost hC)
  sandwiched_logCard_upper := by
    intro ε α hε_nonneg hε_lt_one hα n _hn M _ _ _ EA _ _ EB _ _ C hC
    exact
      (C.asBlockOneShot).log_card_le_channel_sandwichedRenyiMutualInformationE_add
        hε_nonneg hε_lt_one hα (C.asBlockOneShot_maxErrorAtMost hC)

/-- Khatri--Wilde asymptotic upper and strong-converse bounds from the completed
sandwiched-Renyi route.

This closes the source-shaped route in Chapters/EA_capacity.tex:1902-1906: the
one-shot upper bound is lifted to all blocklengths, the sandwiched-Renyi channel
quantity is additive and tends to `I(N)` as `α -> 1+`, and the lower-bound
achievability theorem supplies the nonempty achievable-rate set needed for the
capacity inequalities. -/
theorem entanglementAssisted_asymptoticUpperBounds_of_sandwichedLimit
    [Nonempty a] [Nonempty b] :
    N.IsEntanglementAssistedClassicalRateUpperBound
        N.entanglementAssistedInformation ∧
      N.IsStrongConverseEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation ∧
      N.entanglementAssistedClassicalCapacity ≤
        N.entanglementAssistedInformation ∧
      N.strongConverseEntanglementAssistedClassicalCapacity ≤
        N.entanglementAssistedInformation := by
  exact N.entanglementAssisted_asymptoticUpperBounds_of_sourceAsymptoticUpperInput
    (N.entanglementAssistedInformation_isAchievable_of_oneShotPetzLowerBound)
    (N.entanglementAssisted_sourceAsymptoticUpperInput_of_sandwichedLimit)

/-- Source-shaped Khatri--Wilde converse bundle.

The first component records both finite-block per-code inequalities.  The
remaining components are the asymptotic upper-rate, strong-converse-rate, and
capacity conclusions obtained from additivity and the sandwiched-Renyi
right-limit at `α = 1`.
-/
theorem entanglementAssisted_converse_source_bundle
    [Nonempty a] [Nonempty b] :
    N.EntanglementAssistedFiniteBlockUpperBounds ∧
      N.IsEntanglementAssistedClassicalRateUpperBound
          N.entanglementAssistedInformation ∧
      N.IsStrongConverseEntanglementAssistedClassicalRate
          N.entanglementAssistedInformation ∧
      N.entanglementAssistedClassicalCapacity ≤
          N.entanglementAssistedInformation ∧
      N.strongConverseEntanglementAssistedClassicalCapacity ≤
          N.entanglementAssistedInformation := by
  exact ⟨N.entanglementAssisted_finiteBlockUpperBounds,
    N.entanglementAssisted_asymptoticUpperBounds_of_sandwichedLimit⟩

/-- Final Khatri--Wilde entanglement-assisted classical communication capacity
identity, assembled from the one-shot Petz lower bound and the sandwiched-Renyi
strong-converse route.

The conclusion is the Lean version of
`C_EA(N) = \widetilde C_EA(N) = I(N)`: both the operational capacity and the
strong-converse capacity are equal to the channel mutual information. -/
theorem entanglementAssisted_capacity_and_strongConverseCapacity_eq_information_of_sandwichedLimit
    [Nonempty a] [Nonempty b] :
    N.entanglementAssistedClassicalCapacity = N.entanglementAssistedInformation ∧
      N.strongConverseEntanglementAssistedClassicalCapacity =
        N.entanglementAssistedInformation := by
  exact N.entanglementAssisted_capacity_and_strongConverseCapacity_eq_information_of_sourceConverseWitness
    (N.entanglementAssistedInformation_isAchievable_of_oneShotPetzLowerBound)
    (N.entanglementAssisted_sourceConverseWitnessFamily_of_sourceAsymptoticUpperInput
      (N.entanglementAssisted_sourceAsymptoticUpperInput_of_sandwichedLimit))

end Channel

end

end QIT
