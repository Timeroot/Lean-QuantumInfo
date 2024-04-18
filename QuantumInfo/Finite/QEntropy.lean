import Mathlib
import QuantumInfo.Finite.QState
import QuantumInfo.Finite.Entropy

/-
Quantum notions of information and entropy.
-/

noncomputable section

variable {d d₁ d₂ : Type*} [Fintype d] [Fintype d₁] [Fintype d₂]

/-- Von Neumann entropy of a mixed state. -/
def Sᵥₙ (ρ : MState d) : ℝ :=
  Hₛ (ρ.spectrum)

/-- The Quantum Conditional Entropy S(ρᴬ|ρᴮ) is given by S(ρᴬᴮ) - S(ρᴮ). -/
def QConditionalEnt (ρ : MState (d₁ × d₂)) : ℝ :=
  Sᵥₙ ρ - Sᵥₙ ρ.trace_left

/-- The Quantum Mutual Information I(A:B) is given by S(A) + S(B) - S(AB). -/
def QMutualInfo (ρ : MState (d₁ × d₂)) : ℝ :=
  Sᵥₙ ρ.trace_left + Sᵥₙ ρ.trace_right - Sᵥₙ ρ

/-- The Coherent Information of a state ρ pasing through a channel Λ is the negative conditional
  entropy of the image under Λ of the purification of ρ. -/
def CoherentInfo (ρ : MState d₁) (Λ : QChannel d₁ d₂) : ℝ :=
  let ρPure : MState (d₁ × d₁) := MState.pure ρ.purify
  let ρImg : MState (d₂ × d₁) := (Λ.prod (QChannel.id d₁)) ρPure
  (- QConditionalEnt ρImg)

/-- The quantum relative entropy S(ρ‖σ) = Tr[ρ (log ρ - log σ)]. -/
def QRelativeEnt (ρ σ : MState d) : ℝ :=
  sorry

--Quantum discord

--Entanglement:
-- * Entanglement entropy
-- * Entanglement of formation
-- * Relative entropy of entanglement
-- * Squashed entanglement
-- * Negativity (+ facts here: https://www.quantiki.org/wiki/strong-sub-additivity)
-- * Distillable entanglement (One way, Two way, --> Coherent Information)
-- * Entanglement cost (!= EoF, prove; asymptotically == EoF.)
-- Bound entanglement (Prop)

namespace Entropy

--https://en.wikipedia.org/wiki/Von_Neumann_entropy#Properties
--  in particular https://www.quantiki.org/wiki/strong-sub-additivity

--https://en.wikipedia.org/wiki/Quantum_relative_entropy#Relation_to_other_quantum_information_quantities

--QMutualInfo is symmetric

--TODO:
-- * Classical conditional entropy is nonnegative
-- * Not true of QConditionalS
-- * These measures track their classical values

/-- I(A:B) = S(AB‖ρᴬ⊗ρᴮ) -/
theorem QMutualInfo_as_QRelativeEnt (ρ : MState (d₁ × d₂)) :
    QMutualInfo ρ = QRelativeEnt ρ (ρ.trace_right ⊗ ρ.trace_left) :=
  sorry

end Entropy
