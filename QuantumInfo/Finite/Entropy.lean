import QuantumInfo.Finite.Braket
import QuantumInfo.Finite.CPTPMap
import ClassicalInfo.Entropy

/-
Quantum notions of information and entropy.
-/

noncomputable section

variable {d d₁ d₂ d₃ : Type*} [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃] [DecidableEq d₁] [DecidableEq d₂]

/-- Von Neumann entropy of a mixed state. -/
def Sᵥₙ (ρ : MState d) : ℝ :=
  Hₛ (ρ.spectrum)

/-- The Quantum Conditional Entropy S(ρᴬ|ρᴮ) is given by S(ρᴬᴮ) - S(ρᴮ). -/
def QConditionalEnt (ρ : MState (d₁ × d₂)) : ℝ :=
  Sᵥₙ ρ - Sᵥₙ ρ.trace_left

/-- The Quantum Mutual Information I(A:B) is given by S(ρᴬ) + S(ρᴮ) - S(ρᴬᴮ). -/
def QMutualInfo (ρ : MState (d₁ × d₂)) : ℝ :=
  Sᵥₙ ρ.trace_left + Sᵥₙ ρ.trace_right - Sᵥₙ ρ

/-- The Coherent Information of a state ρ pasing through a channel Λ is the negative conditional
  entropy of the image under Λ of the purification of ρ. -/
def CoherentInfo (ρ : MState d₁) (Λ : CPTPMap d₁ d₂) : ℝ :=
  let ρPure : MState (d₁ × d₁) := MState.pure ρ.purify
  let ρImg : MState (d₂ × d₁) := Λ.prod CPTPMap.id ρPure
  (- QConditionalEnt ρImg)

/-- The quantum relative entropy S(ρ‖σ) = Tr[ρ (log ρ - log σ)]. -/
def QRelativeEnt (ρ σ : MState d) [DecidableEq d] : ℝ :=
  (ρ.m * (ρ.pos.log - σ.pos.log)).trace.re

/-- The Quantum Conditional Mutual Information, I(A;C|B) = S(A|B) - S(A|BC). -/
def QCMI (ρ : MState (d₁ × d₂ × d₃)) : ℝ :=
  sorry

--QConditionalEnt chain rule
--TODO: QCMI =  I(A;C|B) = S(A|B) - S(A|BC).
--QCMI chain rule

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

-- https://arxiv.org/pdf/quant-ph/0406162

--https://en.wikipedia.org/wiki/Von_Neumann_entropy#Properties
--  in particular https://www.quantiki.org/wiki/strong-sub-additivity

--https://en.wikipedia.org/wiki/Quantum_relative_entropy#Relation_to_other_quantum_information_quantities

--QMutualInfo is symmetric

--TODO:
-- * Classical conditional entropy is nonnegative
-- * Not true of QConditionalS
-- * These measures track their classical values

namespace Entropy
open Classical

/-- von Neumman entropy is nonnegative. -/
theorem Sᵥₙ_nonneg (ρ : MState d) : 0 ≤ Sᵥₙ ρ :=
  Hₛ_nonneg _

/-- von Neumman entropy is at most log d. -/
theorem Sᵥₙ_le_log_d (ρ : MState d) : Sᵥₙ ρ ≤ Real.log (Finset.card Finset.univ (α := d)):=
  Hₛ_le_log_d _

/-- von Neumman entropy of pure states is zero. -/
@[simp]
theorem Sᵥₙ_of_pure_zero (ψ : Ket d) : Sᵥₙ (MState.pure ψ) = 0 := by
  obtain ⟨i, hi⟩ := MState.spectrum_pure_eq_constant ψ
  rw [Sᵥₙ, hi, Hₛ_constant_eq_zero]

/-- von Neumann entropy is unchanged under SWAP. TODO: All unitaries-/
@[simp]
theorem Sᵥₙ_of_SWAP_eq (ρ : MState (d₁ × d₂)) : Sᵥₙ ρ.SWAP = Sᵥₙ ρ := by
  sorry

/-- von Neumann entropy is unchanged under assoc. -/
@[simp]
theorem Sᵥₙ_of_assoc_eq (ρ : MState ((d₁ × d₂) × d₃)) : Sᵥₙ ρ.assoc = Sᵥₙ ρ := by
  sorry

/-- von Neumann entropy is unchanged under assoc'. -/
theorem Sᵥₙ_of_assoc'_eq (ρ : MState ((d₁ × d₂) × d₃)) : Sᵥₙ ρ.assoc = Sᵥₙ ρ := by
  simp

/-- von Neumman entropies of the left- and right- partial trace of pure states are equal. -/
theorem Sᵥₙ_of_partial_eq (ψ : Ket (d₁ × d₂)) :
    Sᵥₙ (MState.pure ψ).trace_left = Sᵥₙ (MState.pure ψ).trace_right :=
  sorry

/-- Weak monotonicity of quantum conditional entropy. S(A|B) + S(A|C) ≥ 0 -/
theorem weak_monotonicity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    let ρ₁₂ := ρ₁₂₃.assoc'.trace_right
    let ρ₁₃ := ρ₁₂₃.SWAP.assoc.trace_left.SWAP
    0 ≤ QConditionalEnt ρ₁₂ + QConditionalEnt ρ₁₃:=
  sorry

/-- Quantum conditional entropy is symmetric for pure states. -/
@[simp]
theorem QConditionalEnt_of_pure_symm (ψ : Ket (d₁ × d₂)) :
    QConditionalEnt (MState.pure ψ).SWAP = QConditionalEnt (MState.pure ψ) := by
  simp [QConditionalEnt, Sᵥₙ_of_partial_eq]

/-- Quantum mutual information is symmetric. -/
@[simp]
theorem QMutualInfo_symm (ρ : MState (d₁ × d₂)) :
    QMutualInfo ρ.SWAP = QMutualInfo ρ := by
  simp [QMutualInfo, add_comm]

/-- I(A:B) = S(AB‖ρᴬ⊗ρᴮ) -/
theorem QMutualInfo_as_QRelativeEnt (ρ : MState (d₁ × d₂)) :
    QMutualInfo ρ = QRelativeEnt ρ (ρ.trace_right ⊗ ρ.trace_left) :=
  sorry

/-- "Ordinary" subadditivity of von Neumann entropy -/
theorem S_subadditivity (ρ : MState (d₁ × d₂)) :
    Sᵥₙ ρ ≤ Sᵥₙ ρ.trace_right + Sᵥₙ ρ.trace_left :=
  sorry

universe u_5

section foo

open Lean.Elab.Command

aux_def wlog : ∀ (d₁ : Type _) {d₂ : Type _} [Fintype d₁] [Fintype d₂]
      (ρ : MState (d₁ × d₂)), Sᵥₙ (MState.trace_right ρ) - Sᵥₙ (MState.trace_left ρ) ≤ Sᵥₙ ρ :=
    sorry

/-- Araki-Lieb triangle inequality on vN entropy -/
theorem S_triangle_subaddivity (ρ : MState (d₁ × d₂)) :
    abs (Sᵥₙ ρ.trace_right - Sᵥₙ ρ.trace_left) ≤ Sᵥₙ ρ :=
  sorry

end foo

/-- Strong subadditivity on a tripartite system -/
theorem S_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    let ρ₁₂ := ρ₁₂₃.assoc'.trace_right;
    let ρ₂₃ := ρ₁₂₃.trace_left;
    let ρ₂ := ρ₁₂₃.trace_left.trace_right;
    Sᵥₙ ρ₁₂₃ + Sᵥₙ ρ₂ ≤ Sᵥₙ ρ₁₂ + Sᵥₙ ρ₂₃ :=
  sorry

/-- Strong subadditivity, stated in terms of conditional entropies.
  Also called the data processing inequality. H(A|BC) ≤ H(A|B). -/
theorem QConditionalEnt_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    QConditionalEnt ρ₁₂₃ ≤ QConditionalEnt (ρ₁₂₃.assoc'.trace_right) := by
  have := S_strong_subadditivity ρ₁₂₃
  dsimp at this
  simp only [QConditionalEnt, MState.trace_right_left_assoc']
  linarith

/-- Strong subadditivity, stated in terms of quantum mutual information.
  I(A;BC) ≥ I(A;B). -/
theorem QMutualInfo_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    QMutualInfo ρ₁₂₃ ≥ QMutualInfo (ρ₁₂₃.assoc'.trace_right) := by
  have := S_strong_subadditivity ρ₁₂₃
  dsimp at this
  simp only [QMutualInfo, MState.trace_right_left_assoc', MState.trace_right_right_assoc']
  linarith

end Entropy
