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

proof_wanted inner_conj_unitary {n : Type*} [Fintype n] [DecidableEq n]
  (A B : HermitianMat n ℂ) (U : 𝐔[n]) :
    (A.conj U.val).inner (B.conj U.val) = A.inner B

/-- No-cloning -/
theorem no_cloning (ψ φ f : Ket d) (U : 𝐔[d × d]) (hψ : (pure (ψ ⊗ f)).U_conj U = pure (ψ ⊗ ψ)) (hφ : (pure (φ ⊗ f)).U_conj U = pure (φ ⊗ φ)) (H : (pure ψ).inner (pure φ) < (1 : ℝ)) :
  (pure ψ).inner (pure φ) = (0 : ℝ) := by
  let ρψ := pure ψ
  let ρφ := pure φ
  have h1 : (((pure (ψ ⊗ ψ)).inner (pure (φ ⊗ φ))) : ℂ) = ρψ.inner ρφ * ρψ.inner ρφ := by
    simp only [pure_prod_pure]
    -- see `MState.lean` for
    -- `inner_sep_apply : ((ξ1⊗ξ2).inner (ψ1⊗ψ2) : ℂ) = (ξ1.inner ψ1) * (ξ2.inner ψ2)`
    rw [inner_sep_apply ρψ ρφ ρψ ρφ]
    simp only [Prob.coe_mul, Complex.ofReal_mul]
  have h2 : (((pure (ψ ⊗ ψ)).inner (pure (φ ⊗ φ))) : ℝ) = ((pure (ψ ⊗ f)).U_conj U).inner ((pure (φ ⊗ f)).U_conj U) := by
    simp only [pure_prod_pure] at hψ hφ ⊢
    rw [hψ, hφ]
  simp [MState.inner, HermitianMat.inner] at h2
  simp [U_conj] at h2
  have hU :
    U.val * (pure (ψ ⊗ f)).m * U.val.conjTranspose * (U.val * (pure (φ ⊗ f)).m * U.val.conjTranspose) =
      U.val * (pure (ψ ⊗ f)).m * (pure (φ ⊗ f)).m * U.val.conjTranspose := by
    calc
      U.val * (pure (ψ ⊗ f)).m * U.val.conjTranspose * (U.val * (pure (φ ⊗ f)).m * U.val.conjTranspose)
          = U.val * (pure (ψ ⊗ f)).m * (U.val.conjTranspose * U.val) * (pure (φ ⊗ f)).m * U.val.conjTranspose := by
        repeat rw [← mul_assoc]
      _ = U.val * (pure (ψ ⊗ f)).m * ((star U.val) * U.val) * (pure (φ ⊗ f)).m * U.val.conjTranspose := by
        -- replace conjTranspose by Matrix.star
        rw [← Matrix.star_eq_conjTranspose]
      _ = U.val * (pure (ψ ⊗ f)).m * (1 : Matrix (d × d) (d × d) ℂ) * (pure (φ ⊗ f)).m * U.val.conjTranspose := by
        -- use the unitary property Matrix.star U * U = 1
        rw [Matrix.UnitaryGroup.star_mul_self U]
      _ = U.val * (pure (ψ ⊗ f)).m * (pure (φ ⊗ f)).m * U.val.conjTranspose := by
        simp [mul_one]
  have hinner : MState.inner (pure ψ ⊗ pure f) (pure φ ⊗ pure f) = ((pure ψ ⊗ pure f).m * (pure φ ⊗ pure f).m).trace.re := by
    simp [MState.inner, HermitianMat.inner, IsMaximalSelfAdjoint.selfadjMap, RCLike.re]
  conv at h2 =>
    rhs
    congr
    simp [HermitianMat.conj, HermitianMat.trace_conj_unitary]
    rw [MState.m]; dsimp
    simp [HermitianMat.conj]
    conv =>
      rhs
      congr; rfl
      rw [MState.m]; dsimp
      simp [HermitianMat.conj]
    rw [hU]
    rw [Matrix.trace_mul_comm (U.val * (pure (ψ ⊗ f)).m * (pure (φ ⊗ f)).m) (U.val).conjTranspose]
    repeat rw [← mul_assoc]
    conv =>
      congr; congr
      lhs
      rw [← Matrix.star_eq_conjTranspose, Matrix.UnitaryGroup.star_mul_self U]
    simp [pure_prod_pure]
    congr; congr
    . rw [prod]; dsimp [MState.m]; simp
    . rw [prod]; dsimp [MState.m]; simp
  conv at h2 =>
    rhs
    congr; congr
    rw [← Matrix.mul_kronecker_mul (pure ψ).m (pure φ).m (pure f).m (pure f).m]
    arg 3
    rw [pure_mul_self f]
  conv_rhs at h2 =>
    rw [Matrix.trace_kronecker]
    simp only [toMat_M, tr', mul_one]
  apply_fun (fun r => (r : ℂ)) at h2
  have h3 := Eq.trans h1.symm h2
  have h4 : ((ρψ.m * ρφ.m).trace.re) * ((ρψ.m * ρφ.m).trace.re - 1) = (0 : ℝ) := by
    rw [← Complex.ofReal_mul, Complex.ofReal_inj] at h3
    rw [mul_sub, sub_eq_zero, mul_one]
    exact h3
  have H' : (pure ψ).inner (pure φ) ≠ (1 : ℝ) := by
    exact H.ne
  apply mul_eq_zero.mp at h4
  apply Or.resolve_right at h4
  have h5 : ¬((pure ψ).m * (pure φ).m).trace.re - 1 = 0 := by
    exact sub_ne_zero_of_ne H'
  exact h4 h5

end MState
