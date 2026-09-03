/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Asymptotic.Upper.Witness

/-!
# Asymptotic upper-bound assembly helpers

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

/-- Assembly theorem for the source-shaped asymptotic upper-bound route.

This is the intended handoff target after the sandwiched-Renyi additivity and
`α → 1` input is available. -/
theorem entanglementAssisted_asymptoticUpperBounds_of_sourceAsymptoticUpperInput
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (H : N.EntanglementAssistedSourceAsymptoticUpperInput) :
    N.IsEntanglementAssistedClassicalRateUpperBound
        N.entanglementAssistedInformation ∧
      N.IsStrongConverseEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation ∧
      N.entanglementAssistedClassicalCapacity ≤
        N.entanglementAssistedInformation ∧
      N.strongConverseEntanglementAssistedClassicalCapacity ≤
        N.entanglementAssistedInformation := by
  exact
    ⟨N.entanglementAssistedInformation_isRateUpperBound_of_sourceAsymptoticUpperInput H,
      N.entanglementAssistedInformation_isStrongConverseRate_of_sourceAsymptoticUpperInput H,
      N.entanglementAssistedClassicalCapacity_le_information_of_sourceAsymptoticUpperInput
        hach H,
      N.strongConverseEntanglementAssistedClassicalCapacity_le_information_of_sourceAsymptoticUpperInput
        hach H⟩

end Channel

end

end QIT
