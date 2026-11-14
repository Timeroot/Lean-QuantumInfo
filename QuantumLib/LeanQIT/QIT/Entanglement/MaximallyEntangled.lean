/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.MaximallyEntangled

/-!
# Maximally entangled invariants

The invariants are stated directly through the reduced density states.  They
do not depend on a protocol-specific representation of an entangled pair.
-/

@[expose] public section

namespace QIT

universe u v

noncomputable section

namespace PureVector

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Nonempty a]
variable [Fintype b] [DecidableEq b] [Nonempty b]

/-- Both marginals of a bipartite pure vector are the corresponding canonical
maximally mixed states.  This is stronger than maximal entanglement when the
two local dimensions differ. -/
def HasMaximallyMixedMarginals (ψ : PureVector (Prod a b)) : Prop :=
  ψ.state.marginalA = State.maximallyMixed a ∧
    ψ.state.marginalB = State.maximallyMixed b

/-- A bipartite pure vector is maximally entangled when the marginal on a
smaller local system is the canonical maximally mixed state. -/
def IsMaximallyEntangled (ψ : PureVector (Prod a b)) : Prop :=
  (Fintype.card a ≤ Fintype.card b ∧
      ψ.state.marginalA = State.maximallyMixed a) ∨
    (Fintype.card b ≤ Fintype.card a ∧
      ψ.state.marginalB = State.maximallyMixed b)

/-- Maximally mixed marginals imply maximal entanglement. -/
theorem HasMaximallyMixedMarginals.isMaximallyEntangled
    {ψ : PureVector (Prod a b)} (hψ : ψ.HasMaximallyMixedMarginals) :
    ψ.IsMaximallyEntangled := by
  rcases le_total (Fintype.card a) (Fintype.card b) with hab | hba
  · exact Or.inl ⟨hab, hψ.1⟩
  · exact Or.inr ⟨hba, hψ.2⟩

theorem maximallyEntangled_hasMaximallyMixedMarginals (pairing : a ≃ b) :
    (maximallyEntangled pairing).HasMaximallyMixedMarginals := by
  constructor
  · exact maximallyEntangled_marginalA pairing
  · exact maximallyEntangled_marginalB pairing

theorem maximallyEntangled_isMaximallyEntangled (pairing : a ≃ b) :
    (maximallyEntangled pairing).IsMaximallyEntangled :=
  (maximallyEntangled_hasMaximallyMixedMarginals pairing).isMaximallyEntangled

end PureVector

end
end QIT
