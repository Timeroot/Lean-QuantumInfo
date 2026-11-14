/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Asymptotic.ConverseWitness
public import QIT.Coding.EntanglementAssisted.Asymptotic.Upper.Input

/-!
# Asymptotic upper-bound witness consequences

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

/-- The source-shaped asymptotic upper input gives the source-consistent
converse witness family used by the KW strong-converse route. -/
theorem entanglementAssisted_sourceConverseWitnessFamily_of_sourceAsymptoticUpperInput
    (H : N.EntanglementAssistedSourceAsymptoticUpperInput) :
    EntanglementAssistedSourceConverseWitnessFamily N :=
  N.entanglementAssisted_sourceConverseWitnessFamily_of_logCardUpperBounds H.logCard_upper

/-- Ordinary-rate upper-bound consequence of the source-shaped asymptotic
upper input. -/
theorem entanglementAssistedInformation_isRateUpperBound_of_sourceAsymptoticUpperInput
    (H : N.EntanglementAssistedSourceAsymptoticUpperInput) :
    N.IsEntanglementAssistedClassicalRateUpperBound
      N.entanglementAssistedInformation :=
  N.entanglementAssisted_information_isUpperBound_of_sourceConverseWitness
    (N.entanglementAssisted_sourceConverseWitnessFamily_of_sourceAsymptoticUpperInput H)

/-- Strong-converse-rate consequence of the source-shaped asymptotic upper
input. -/
theorem entanglementAssistedInformation_isStrongConverseRate_of_sourceAsymptoticUpperInput
    (H : N.EntanglementAssistedSourceAsymptoticUpperInput) :
    N.IsStrongConverseEntanglementAssistedClassicalRate
      N.entanglementAssistedInformation :=
  N.entanglementAssisted_information_isStrongConverseRate_of_sourceConverseWitness
    (N.entanglementAssisted_sourceConverseWitnessFamily_of_sourceAsymptoticUpperInput H)

/-- Capacity upper-bound consequence of the source-shaped asymptotic upper
input. -/
theorem entanglementAssistedClassicalCapacity_le_information_of_sourceAsymptoticUpperInput
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (H : N.EntanglementAssistedSourceAsymptoticUpperInput) :
    N.entanglementAssistedClassicalCapacity ≤
      N.entanglementAssistedInformation :=
  N.entanglementAssistedClassicalCapacity_le_information_of_sourceConverseWitness
    hach (N.entanglementAssisted_sourceConverseWitnessFamily_of_sourceAsymptoticUpperInput H)

/-- Strong-converse capacity upper-bound consequence of the source-shaped
asymptotic upper input. -/
theorem strongConverseEntanglementAssistedClassicalCapacity_le_information_of_sourceAsymptoticUpperInput
    (hach :
      N.IsAchievableEntanglementAssistedClassicalRate
        N.entanglementAssistedInformation)
    (H : N.EntanglementAssistedSourceAsymptoticUpperInput) :
    N.strongConverseEntanglementAssistedClassicalCapacity ≤
      N.entanglementAssistedInformation :=
  N.strongConverseEntanglementAssistedClassicalCapacity_le_information hach
    (N.entanglementAssistedInformation_isStrongConverseRate_of_sourceAsymptoticUpperInput H)

end Channel

end

end QIT
