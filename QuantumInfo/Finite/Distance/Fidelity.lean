import QuantumInfo.Finite.MState
import QuantumInfo.Finite.CPTPMap

noncomputable section

open Classical
open BigOperators
open ComplexConjugate
open Kronecker
open scoped Matrix ComplexOrder

variable {d : Type*} [Fintype d]

/-- The fidelity of two quantum states. This is the quantum version of the Bhattacharyya coefficient. -/
def Fidelity (ρ σ : MState d) : ℝ :=
  let ρσρ := ρ.pos.sqrt * σ.m * ρ.pos.sqrt
  let ρσρ_PosSemidef : ρσρ.PosSemidef := by
    unfold_let ρσρ
    nth_rewrite 2 [← ρ.pos.posSemidef_sqrt.isHermitian]
    exact σ.pos.mul_mul_conjTranspose_same _
  (ρσρ_PosSemidef.sqrt.trace.re)^2

namespace Fidelity

variable {d d₂ : Type*} [Fintype d] [Fintype d₂] (ρ σ : MState d)

theorem ge_zero : 0 ≤ Fidelity ρ σ :=
  sq_nonneg _

theorem le_one : Fidelity ρ σ ≤ 1 :=
  sorry --submultiplicativity of trace and sqrt

/-- The fidelity, as a `Prob` probability with value between 0 and 1. -/
def prob : Prob :=
  ⟨Fidelity ρ σ, ⟨ge_zero ρ σ, le_one ρ σ⟩⟩

/-- A state has perfect fidelity with itself. -/
theorem self_eq_one : Fidelity ρ ρ = 1 :=
  sorry --Break and recombine sqrts

/-- The fidelity is 1 if and only if the two states are the same. -/
theorem eq_one_iff_self : ρ = σ ↔ Fidelity ρ σ = 1 :=
  ⟨fun h ↦ h ▸ self_eq_one ρ,
  sorry
  ⟩

/-- The fidelity is a symmetric quantity. -/
theorem symm : Fidelity ρ σ = Fidelity σ ρ :=
  sorry --break into sqrts

/-- The fidelity cannot increase under the application of a channel. -/
theorem channel_nondecreasing (Λ : CPTPMap d d₂) : Fidelity (Λ ρ) (Λ σ) ≥ Fidelity ρ σ :=
  sorry

--TODO: Arccos ∘ Fidelity forms a metric (triangle inequality), the Fubini–Study metric.
--Matches with classical (squared) Bhattacharyya coefficient
--Invariance under unitaries
--Uhlmann's theorem

end Fidelity
