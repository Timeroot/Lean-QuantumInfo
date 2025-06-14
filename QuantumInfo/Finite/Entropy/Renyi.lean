import QuantumInfo.Finite.Entropy.Defs

/-! # Quantum Relative Entropy and α-Renyi Entropy -/

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The quantum relative entropy S(ρ‖σ) = Tr[ρ (log ρ - log σ)]. -/
@[irreducible]
noncomputable def qRelativeEnt (ρ : MState d) (σ : HermitianMat d ℂ) : ENNReal :=
  open Classical in (if σ.ker ≤ ρ.M.ker then
    some ⟨ρ.exp_val (HermitianMat.log ρ - HermitianMat.log σ),
    /- Quantum relative entropy is nonnegative. This can be proved by an application of
    Klein's inequality. -/
    sorry⟩
  else
    ⊤)

notation "𝐃(" ρ "‖" σ ")" => qRelativeEnt ρ σ

instance : RelEntropy qRelativeEnt where
  DPI := sorry
  of_kron := sorry
  normalized := sorry

instance : RelEntropy.Nontrivial qRelativeEnt where
  nontrivial := sorry

/-- Quantum relative entropy as `Tr[ρ (log ρ - log σ)]` when supports are correct. -/
theorem qRelativeEnt_ker {ρ σ : MState d} (h : σ.M.ker ≤ ρ.M.ker) :
    (𝐃(ρ‖σ) : EReal) = ρ.M.inner (HermitianMat.log ρ - HermitianMat.log σ) := by
  simp only [qRelativeEnt, h]
  congr
