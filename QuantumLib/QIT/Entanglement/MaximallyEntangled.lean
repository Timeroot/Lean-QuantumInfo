/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.States.MaximallyEntangled

/-!
# Maximally entangled invariants

The invariants are stated directly through the reduced density states.  They
do not depend on a protocol-specific representation of an entangled pair.
-/

@[expose] public section

namespace QIT

universe u v

noncomputable section

end
end QIT

namespace Ket

noncomputable section

open QIT
universe u v

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Nonempty a]
variable [Fintype b] [DecidableEq b] [Nonempty b]

/-- Both marginals of a bipartite ket are the corresponding canonical
maximally mixed states.  This is stronger than maximal entanglement when the
two local dimensions differ. -/
def HasMaximallyMixedMarginals (ψ : Ket (a × b)) : Prop :=
  ψ.state.traceRight = (MState.uniform : MState a) ∧
    ψ.state.traceLeft = (MState.uniform : MState b)

/-- A bipartite ket is maximally entangled when the marginal on a
smaller local system is the canonical maximally mixed state. -/
def IsMaximallyEntangled (ψ : Ket (a × b)) : Prop :=
  (Fintype.card a ≤ Fintype.card b ∧
      ψ.state.traceRight = (MState.uniform : MState a)) ∨
    (Fintype.card b ≤ Fintype.card a ∧
      ψ.state.traceLeft = (MState.uniform : MState b))

/-- Maximally mixed marginals imply maximal entanglement. -/
theorem HasMaximallyMixedMarginals.isMaximallyEntangled
    {ψ : Ket (a × b)} (hψ : ψ.HasMaximallyMixedMarginals) :
    ψ.IsMaximallyEntangled := by
  rcases le_total (Fintype.card a) (Fintype.card b) with hab | hba
  · exact Or.inl ⟨hab, hψ.1⟩
  · exact Or.inr ⟨hba, hψ.2⟩

theorem maximallyEntangled_hasMaximallyMixedMarginals (pairing : a ≃ b) :
    (maximallyEntangled pairing).HasMaximallyMixedMarginals := by
  constructor
  · exact maximallyEntangled_traceRight pairing
  · exact maximallyEntangled_traceLeft pairing

theorem maximallyEntangled_isMaximallyEntangled (pairing : a ≃ b) :
    (maximallyEntangled pairing).IsMaximallyEntangled :=
  (maximallyEntangled_hasMaximallyMixedMarginals pairing).isMaximallyEntangled

end

end Ket

namespace QIT
noncomputable section

universe u v

end
end QIT
