/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg, Rodolfo Soldati
-/
import QuantumInfo.Finite.MState

/-! # Unitary operators on quantum state

This file is intended for lemmas about unitary matrices (`Matrix.unitaryGroup`) and how they apply to
`Bra`s, `Ket`s, and `MState` mixed states.

This is imported by `CPTPMap` to define things like unitary channels, Kraus operators, and
complementary channels, so this file itself does not discuss channels yet. -/

noncomputable section

notation "𝐔[" n "]" => Matrix.unitaryGroup n ℂ

namespace HermitianMat

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
variable (A B : HermitianMat n 𝕜) (U : Matrix.unitaryGroup n 𝕜)

@[simp]
theorem trace_conj_unitary : (A.conj U.val).trace = A.trace := by
  simp [Matrix.trace_mul_cycle, HermitianMat.conj, ← Matrix.star_eq_conjTranspose, HermitianMat.trace]

@[simp]
theorem le_conj_unitary : A.conj U.val ≤ B.conj U ↔ A ≤ B := by
  rw [← sub_nonneg, ← sub_nonneg (b := A), ← map_sub]
  constructor
  · intro h
    simpa [HermitianMat.conj_conj] using HermitianMat.conj_le h (star U).val
  · exact fun h ↦ HermitianMat.conj_le h U.val

@[simp]
theorem inner_conj_unitary : (A.conj U.val).inner (B.conj U.val) = A.inner B := by
  dsimp [conj]
  simp only [val_eq_coe, inner_eq_re_trace, mk_toMat]
  rw [← mul_assoc, ← mul_assoc, mul_assoc _ _ U.val]
  rw [Matrix.trace_mul_cycle, ← mul_assoc, ← mul_assoc _ _ A.toMat]
  simp [← Matrix.star_eq_conjTranspose]

/--
The eigenvalues of a Hermitian matrix conjugated by a unitary matrix are the same as the eigenvalues of the original matrix.
-/
@[simp]
theorem eigenvalues_conj {n : Type*} [Fintype n] [DecidableEq n]
    (A : HermitianMat n ℂ) (U : Matrix.unitaryGroup n ℂ) :
    (A.conj U.val).H.eigenvalues = A.H.eigenvalues := by
  -- Since $U$ is unitary, $U * A * Uᴴ$ is similar to $A$.
  have h_similar : (U.val * A.toMat * U.val.conjTranspose).charpoly = A.toMat.charpoly := by
    have h_charpoly : (U.val * A.toMat * U.val.conjTranspose).charpoly = (A.toMat).charpoly := by
      have h_unitary : U.val * U.val.conjTranspose = 1 := by
        exact U.2.2
      have h_charpoly : (U.val * A.toMat * U.val.conjTranspose).charpoly = (A.toMat * U.val.conjTranspose * U.val).charpoly := by
        convert Matrix.charpoly_mul_comm _ _ using 2 ; simp +decide [ Matrix.mul_assoc ];
        simp +decide [ ← mul_assoc, h_unitary ];
        rw [ Matrix.mul_eq_one_comm.mp h_unitary ] ; simp +decide [ mul_assoc ];
        rw [ Matrix.mul_eq_one_comm.mp h_unitary, mul_one ];
      rw [ h_charpoly, Matrix.mul_assoc ];
      rw [ Matrix.mul_eq_one_comm.mp h_unitary, mul_one ];
    exact h_charpoly;
  exact?

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

/-- `MState.U_conj`, the action of a unitary on a mixed state by conjugation.
The ◃ notation comes from the theory of racks and quandles, where this is a
conjugation-like operation. -/
scoped[MState] notation:80 U:80 " ◃ " ρ:81 => MState.U_conj ρ U

/-- You might think this should only be true up to permutation, so that it would read like
`∃ σ : Equiv.Perm d, (ρ.U_conj U).spectrum = ρ.spectrum.relabel σ`. But since eigenvalues
of a matrix are always canonically sorted, this is actually an equality.
-/
@[simp]
theorem U_conj_spectrum_eq (ρ : MState d) (U : 𝐔[d]) :
    (ρ.U_conj U).spectrum = ρ.spectrum := by
  simp [MState.spectrum, U_conj]

@[simp]
theorem inner_U_conj (ρ σ : MState d) (U : 𝐔[d]) : ⟪U ◃ ρ, U ◃ σ⟫ = ⟪ρ, σ⟫ := by
  simp [U_conj, MState.inner]

/-- The **No-cloning theorem**, saying that if states `ψ` and `φ` can both be perfectly cloned using a
unitary `U` and a fiducial state `f`, and they aren't identical (their inner product is less than 1),
then the two states must be orthogonal to begin with. In short: only orthogonal states can be simultaneously
cloned. -/
theorem no_cloning {ψ φ f : Ket d} {U : 𝐔[d × d]}
  (hψ : U ◃ pure (ψ ⊗ f) = pure (ψ ⊗ ψ))
  (hφ : U ◃ pure (φ ⊗ f) = pure (φ ⊗ φ))
  (H : ⟪pure ψ, pure φ⟫ < (1 : ℝ)) :
    ⟪pure ψ, pure φ⟫ = (0 : ℝ) := by
  set ρψ := pure ψ
  set ρφ := pure φ
  have h1 : ⟪ρψ, ρφ⟫ * ⟪ρψ, ρφ⟫ = ⟪pure (ψ ⊗ ψ), pure (φ ⊗ φ)⟫ := by
    -- From `MState.lean`: `prod_inner_prod : ⟪ξ1⊗ξ2, ψ1⊗ψ2⟫ = ⟪ξ1, ψ1⟫ * ⟪ξ2, ψ2⟫`
    grind only [pure_prod_pure, prod_inner_prod]
  have h2 : (⟪pure (ψ ⊗ ψ), pure (φ ⊗ φ)⟫ : ℝ) = ⟪U ◃ pure (ψ ⊗ f), U ◃ pure (φ ⊗ f)⟫ := by
    grind only [pure_prod_pure]
  replace h2 : ((pure (ψ ⊗ ψ)).m * (pure (φ ⊗ φ)).m).trace.re = (ρψ.m * ρφ.m).trace.re := by
    convert ← h2
    simp +zetaDelta only [inner_U_conj, pure_prod_pure, prod]
    simp [inner, HermitianMat.inner_eq_re_trace, ← Matrix.mul_kronecker_mul, pure_mul_self,
      Matrix.trace_kronecker]
  have h3 : ((ρψ.m * ρφ.m).trace.re) * ((ρψ.m * ρφ.m).trace.re - 1) = 0 := by
    rw [mul_sub, sub_eq_zero, mul_one]
    exact congr(Subtype.val $h1).trans h2
  rw [mul_eq_zero] at h3
  apply h3.resolve_right
  exact sub_ne_zero_of_ne H.ne

end MState
