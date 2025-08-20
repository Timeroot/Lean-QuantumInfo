import QuantumInfo.Finite.MState

/-! # Unitary operators on quantum state

This file is intended for lemmas about unitary matrices (`Matrix.unitaryGroup`) and how they apply to
`Bra`s, `Ket`s, and `MState` mixed states.

This is imported by `CPTPMap` to define things like unitary channels, Kraus operators, and
complementary channels, so this file itself does not discuss channels yet.-/

noncomputable section

notation "𝐔[" n "]" => Matrix.unitaryGroup n ℂ

namespace HermitianMat

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
variable (A B : HermitianMat n 𝕜) (U : Matrix.unitaryGroup n 𝕜)

--PULLOUT
omit [DecidableEq n] in
theorem add_conj (M : Matrix m n 𝕜) : (A + B).conj M = A.conj M + B.conj M := by
  ext1
  simp [conj, Matrix.mul_add, Matrix.add_mul]

omit [DecidableEq n] in
theorem sub_conj (M : Matrix m n 𝕜) : (A - B).conj M = A.conj M - B.conj M := by
  ext1
  simp [conj, Matrix.mul_sub, Matrix.sub_mul]

@[simp]
theorem conj_one : A.conj (1 : Matrix n n 𝕜) = A := by
  simp [conj]
--PULLOUT

@[simp]
theorem trace_conj_unitary : (A.conj U.val).trace = A.trace := by
  simp [Matrix.trace_mul_cycle, HermitianMat.conj, ← Matrix.star_eq_conjTranspose, HermitianMat.trace]

@[simp]
theorem le_conj_unitary : A.conj U.val ≤ B.conj U ↔ A ≤ B := by
  rw [← sub_nonneg, ← sub_nonneg (b := A), ← sub_conj]
  constructor
  · intro h
    simpa [HermitianMat.conj_conj] using HermitianMat.conj_le h (star U).val
  · exact fun h ↦ HermitianMat.conj_le h U.val

end HermitianMat

namespace MState

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d]

/-- Conjugate a state by a unitary matrix (applying the unitary as an evolution). -/
def U_conj (ρ : MState d) (U : 𝐔[d]) : MState d where
  M := ρ.M.conj U.val
  tr := by simp
  zero_le := HermitianMat.conj_le ρ.zero_le U.val

/-- You might think this should only be true up to permutation, so that it would read like
`∃ σ : Equiv.Perm d, (ρ.U_conj U).spectrum = ρ.spectrum.relabel σ`. But since eigenvalues
of a matrix are always canonically sorted, this is actually an equality.
-/
@[simp]
theorem U_conj_spectrum_eq (ρ : MState d) (U : 𝐔[d]) :
    (ρ.U_conj U).spectrum = ρ.spectrum := by
  have (M : HermitianMat d ℂ) (U : 𝐔[d]) : (M.conj U).H.eigenvalues = M.H.eigenvalues := by
    --missing simp lemma
    sorry
  simp [MState.spectrum, U_conj, this]

end MState
