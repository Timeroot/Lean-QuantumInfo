import QuantumInfo.Finite.MState

/-! # Unitary operators on quantum state

This file is intended for lemmas about unitary matrices (`Matrix.unitaryGroup`) and how they apply to
`Bra`s, `Ket`s, and `MState` mixed states.

This is imported by `CPTPMap` to define things like unitary channels, Kraus operators, and
complementary channels, so this file itself does not discuss channels yet.-/

noncomputable section

namespace MState

notation "𝐔[" n "]" => Matrix.unitaryGroup n ℂ

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d]

/-- Conjugate a state by a unitary matrix (applying the unitary as an evolution). -/
def U_conj (ρ : MState d) (U : 𝐔[d]) : MState d where
  val := U * ρ.m * star U
  property := by simp [Matrix.IsHermitian, MState.m, ρ.pos.1.eq, Matrix.star_eq_conjTranspose, mul_assoc]
  tr := by simp [Matrix.trace_mul_cycle, ρ.tr, MState.m]
  pos := ⟨by simp [Matrix.IsHermitian, MState.m, ρ.pos.1.eq, Matrix.star_eq_conjTranspose, mul_assoc],
    by
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    convert ρ.pos.2 (Matrix.mulVec (↑(star U)) x)
    simp [Matrix.star_mulVec, Matrix.star_eq_conjTranspose]
    ⟩

theorem U_conj_spectrum_eq (ρ : MState d) (U : 𝐔[d]) : ∃ σ : d ≃ d,
    (ρ.U_conj U).spectrum = ρ.spectrum.relabel σ := by
  --Each eigenvector v for ρ yields an eigenvector U† v for U† ρ U.
  --Applying this both ways, get a correspondence between the spectra.
  --Sadly this doesn't prove multiplicities match up.
  --Need a statement like "diagonalization is unique up to permutation".
  sorry

end MState
