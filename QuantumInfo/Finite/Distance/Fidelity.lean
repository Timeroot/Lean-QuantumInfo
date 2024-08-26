import QuantumInfo.Finite.MState
import QuantumInfo.Finite.CPTPMap

noncomputable section

open Classical
open BigOperators
open ComplexConjugate
open Kronecker
open scoped Matrix ComplexOrder

variable {d d₂ : Type*} [Fintype d] [Fintype d₂] (ρ σ : MState d)

--We put all of the fidelity defs and theorems in the MState namespace so that they have the
--nice . syntax, i.e. `ρ.Fidelity σ = 1 ↔ ρ = σ`.
namespace MState

/-- The fidelity of two quantum states. This is the quantum version of the Bhattacharyya coefficient. -/
def fidelity (ρ σ : MState d) : ℝ :=
  let ρσρ := ρ.pos.sqrt * σ.m * ρ.pos.sqrt
  let ρσρ_PosSemidef : ρσρ.PosSemidef := by
    unfold_let ρσρ
    nth_rewrite 2 [← ρ.pos.posSemidef_sqrt.isHermitian]
    exact σ.pos.mul_mul_conjTranspose_same _
  (ρσρ_PosSemidef.sqrt.trace.re)^2

theorem fidelity_ge_zero : 0 ≤ fidelity ρ σ :=
  sq_nonneg _

theorem fidelity_le_one : fidelity ρ σ ≤ 1 :=
  sorry --submultiplicativity of trace and sqrt

/-- The fidelity, as a `Prob` probability with value between 0 and 1. -/
def fidelity_prob : Prob :=
  ⟨fidelity ρ σ, ⟨fidelity_ge_zero ρ σ, fidelity_le_one ρ σ⟩⟩

/-- A state has perfect fidelity with itself. -/
theorem fidelity_self_eq_one : fidelity ρ ρ = 1 :=
  sorry --Break and recombine sqrts

/-- The fidelity is 1 if and only if the two states are the same. -/
theorem fidelity_eq_one_iff_self : fidelity ρ σ = 1 ↔ ρ = σ :=
  ⟨sorry,
  fun h ↦ h ▸ fidelity_self_eq_one ρ
  ⟩

/-- The fidelity is a symmetric quantity. -/
theorem fidelity_symm : fidelity ρ σ = fidelity σ ρ :=
  sorry --break into sqrts

/-- The fidelity cannot increase under the application of a channel. -/
theorem fidelity_channel_nondecreasing (Λ : CPTPMap d d₂) : fidelity (Λ ρ) (Λ σ) ≥ fidelity ρ σ :=
  sorry

--TODO: Real.arccos ∘ fidelity forms a metric (triangle inequality), the Fubini–Study metric.
--Matches with classical (squared) Bhattacharyya coefficient
--Invariance under unitaries
--Uhlmann's theorem

end MState
