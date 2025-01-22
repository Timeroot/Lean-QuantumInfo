import QuantumInfo.Finite.Braket
import QuantumInfo.Finite.CPTPMap
import ClassicalInfo.Entropy

/-!
Quantum notions of information and entropy.
-/

noncomputable section

variable {d d₁ d₂ d₃ : Type*} [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃] [DecidableEq d₁] [DecidableEq d₂]
variable {dA dB dC dA₁ dA₂ : Type*} [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂][DecidableEq dA] [DecidableEq dB] [DecidableEq dA₁] [DecidableEq dA₂]

/-- Von Neumann entropy of a mixed state. -/
def Sᵥₙ (ρ : MState d) : ℝ :=
  Hₛ (ρ.spectrum)

/-- The Quantum Conditional Entropy S(ρᴬ|ρᴮ) is given by S(ρᴬᴮ) - S(ρᴮ). -/
def qConditionalEnt (ρ : MState (dA × dB)) : ℝ :=
  Sᵥₙ ρ - Sᵥₙ ρ.traceLeft

/-- The Quantum Mutual Information I(A:B) is given by S(ρᴬ) + S(ρᴮ) - S(ρᴬᴮ). -/
def qMutualInfo (ρ : MState (dA × dB)) : ℝ :=
  Sᵥₙ ρ.traceLeft + Sᵥₙ ρ.traceRight - Sᵥₙ ρ

/-- The Coherent Information of a state ρ pasing through a channel Λ is the negative conditional
  entropy of the image under Λ of the purification of ρ. -/
def coherentInfo (ρ : MState d₁) (Λ : CPTPMap d₁ d₂) : ℝ :=
  let ρPure : MState (d₁ × d₁) := MState.pure ρ.purify
  let ρImg : MState (d₂ × d₁) := Λ.prod CPTPMap.id ρPure
  (- qConditionalEnt ρImg)

variable [DecidableEq d]

open Classical in
/-- The quantum relative entropy S(ρ‖σ) = Tr[ρ (log ρ - log σ)]. -/
def qRelativeEnt (ρ σ : MState d)  : EReal :=
  (if
    LinearMap.ker σ.m.toLin' ≤ LinearMap.ker ρ.m.toLin'
  then
    ρ.Hermitian.rinner (ρ.pos.log_IsHermitian.sub σ.pos.log_IsHermitian)
  else
    ⊤)

/-- Quantum relative entropy as `Tr[ρ (log ρ - log σ)]` when supports are correct. -/
theorem qRelativeEnt_ker {ρ σ : MState d} (h : LinearMap.ker σ.m.toLin' ≤ LinearMap.ker ρ.m.toLin') :
    qRelativeEnt ρ σ = ρ.Hermitian.rinner (ρ.pos.log_IsHermitian.sub σ.pos.log_IsHermitian) := by
  simp [qRelativeEnt, h]

/-- Quantum relative entropy when σ has full rank -/
theorem qRelativeEnt_rank {ρ σ : MState d} (h : σ.m.rank = Fintype.card d) :
    qRelativeEnt ρ σ = ρ.Hermitian.rinner (ρ.pos.log_IsHermitian.sub σ.pos.log_IsHermitian) := by
  apply qRelativeEnt_ker
  suffices LinearMap.ker σ.m.toLin' = ⊥ by
    simp only [this, bot_le]
  --TODO this definitely belongs in Mathlib
  rw [LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank rfl]
  rw [← Matrix.toLin_eq_toLin' , Matrix.range_toLin_eq_top]
  apply Ne.isUnit
  rw [Matrix.IsHermitian.det_eq_prod_eigenvalues σ.pos.1]
  rw [Finset.prod_ne_zero_iff]
  intro a _
  simp only [Complex.coe_algebraMap, ne_eq, Complex.ofReal_eq_zero]
  rw [Matrix.IsHermitian.rank_eq_card_non_zero_eigs σ.pos.1, Fintype.card_subtype_compl] at h
  have h₂ : Fintype.card { x // σ.pos.1.eigenvalues x = 0 } = 0 := by
    have : 0 < Fintype.card d := @Fintype.card_pos _ _ σ.nonempty
    omega
  rw [Fintype.card_eq_zero_iff] at h₂
  by_contra h'
  exact h₂.elim ⟨_, h'⟩

--∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    --f (a • x + b • y) ≤ a • f x + b • f y

/-- Quantum relative entropy is nonnegative. (TODO: Should be bundled into ENNReal with `qRelativeEnt`?).
This can be proved by an application of Klein's inequality. -/
theorem qRelativeEnt_nonneg (ρ σ : MState d) : 0 ≤ qRelativeEnt ρ σ := by
  sorry

/-- Joint convexity of Quantum relative entropy. We can't state this with `ConvexOn` because that requires
an `AddCommMonoid`, which `MState`s are not. Instead we state it with `Mixable`.

TODO:
 * Add the `Mixable` instance that infers from the `Coe` so that the right hand side can be written as
`p [qRelativeEnt ρ₁ σ₁ ↔ qRelativeEnt ρ₂ σ₂]`
 * Define (joint) convexity as its own thing - a `ConvexOn` for `Mixable` types.
 * Maybe, more broadly, find a way to make `ConvexOn` work with the subset of `Matrix` that corresponds to `MState`.
-/
theorem qRelativeEnt_joint_convexity :
  ∀ (ρ₁ ρ₂ σ₁ σ₂ : MState d), ∀ (p : Prob),
    qRelativeEnt (p [ρ₁ ↔ ρ₂]) (p [σ₁ ↔ σ₂]) ≤ p * qRelativeEnt ρ₁ σ₁ + (1 - p) * qRelativeEnt ρ₂ σ₂ := by
  sorry

/-- The Quantum Conditional Mutual Information, I(A;C|B) = S(A|B) - S(A|BC). -/
def qcmi (ρ : MState (dA × dB × dC)) : ℝ :=
  qConditionalEnt ρ.assoc'.traceRight - qConditionalEnt ρ

--QConditionalEnt chain rule

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

section entropy
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
theorem Sᵥₙ_of_assoc'_eq (ρ : MState (d₁ × (d₂ × d₃))) : Sᵥₙ ρ.assoc' = Sᵥₙ ρ := by
  sorry

/-- von Neumman entropies of the left- and right- partial trace of pure states are equal. -/
theorem Sᵥₙ_of_partial_eq (ψ : Ket (d₁ × d₂)) :
    Sᵥₙ (MState.pure ψ).traceLeft = Sᵥₙ (MState.pure ψ).traceRight :=
  sorry

/-- Weak monotonicity of quantum conditional entropy. S(A|B) + S(A|C) ≥ 0 -/
theorem Sᵥₙ_weak_monotonicity (ρ : MState (dA × dB × dC)) :
    let ρAB := ρ.assoc'.traceRight
    let ρAC := ρ.SWAP.assoc.traceLeft.SWAP
    0 ≤ qConditionalEnt ρAB + qConditionalEnt ρAC :=
  sorry

/-- Quantum conditional entropy is symmetric for pure states. -/
@[simp]
theorem qConditionalEnt_of_pure_symm (ψ : Ket (d₁ × d₂)) :
    qConditionalEnt (MState.pure ψ).SWAP = qConditionalEnt (MState.pure ψ) := by
  simp [qConditionalEnt, Sᵥₙ_of_partial_eq]

/-- Quantum mutual information is symmetric. -/
@[simp]
theorem qMutualInfo_symm (ρ : MState (d₁ × d₂)) :
    qMutualInfo ρ.SWAP = qMutualInfo ρ := by
  simp [qMutualInfo, add_comm]

/-- I(A:B) = S(AB‖ρᴬ⊗ρᴮ) -/
theorem qMutualInfo_as_qRelativeEnt (ρ : MState (dA × dB)) :
    qMutualInfo ρ = qRelativeEnt ρ (ρ.traceRight ⊗ ρ.traceLeft) :=
  sorry

/-- "Ordinary" subadditivity of von Neumann entropy -/
theorem Sᵥₙ_subadditivity (ρ : MState (d₁ × d₂)) :
    Sᵥₙ ρ ≤ Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft :=
  sorry

-- section triangle_tmp
-- open Lean.Elab.Command
-- aux_def wlog : ∀ (d₁ : Type _) {d₂ : Type _} [Fintype d₁] [Fintype d₂]
--       (ρ : MState (d₁ × d₂)), Sᵥₙ (MState.traceRight ρ) - Sᵥₙ (MState.traceLeft ρ) ≤ Sᵥₙ ρ :=
--     sorry
-- end triangle_tmp

/-- Araki-Lieb triangle inequality on von Neumann entropy -/
theorem Sᵥₙ_triangle_subaddivity (ρ : MState (d₁ × d₂)) :
    abs (Sᵥₙ ρ.traceRight - Sᵥₙ ρ.traceLeft) ≤ Sᵥₙ ρ :=
  sorry

/-- Strong subadditivity on a tripartite system -/
theorem Sᵥₙ_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    let ρ₁₂ := ρ₁₂₃.assoc'.traceRight;
    let ρ₂₃ := ρ₁₂₃.traceLeft;
    let ρ₂ := ρ₁₂₃.traceLeft.traceRight;
    Sᵥₙ ρ₁₂₃ + Sᵥₙ ρ₂ ≤ Sᵥₙ ρ₁₂ + Sᵥₙ ρ₂₃ :=
  sorry

/-- Strong subadditivity, stated in terms of conditional entropies.
  Also called the data processing inequality. H(A|BC) ≤ H(A|B). -/
theorem qConditionalEnt_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    qConditionalEnt ρ₁₂₃ ≤ qConditionalEnt (ρ₁₂₃.assoc'.traceRight) := by
  have := Sᵥₙ_strong_subadditivity ρ₁₂₃
  dsimp at this
  simp only [qConditionalEnt, MState.traceRight_left_assoc']
  linarith

/-- Strong subadditivity, stated in terms of quantum mutual information.
  I(A;BC) ≥ I(A;B). -/
theorem qMutualInfo_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    qMutualInfo ρ₁₂₃ ≥ qMutualInfo (ρ₁₂₃.assoc'.traceRight) := by
  have := Sᵥₙ_strong_subadditivity ρ₁₂₃
  dsimp at this
  simp only [qMutualInfo, MState.traceRight_left_assoc', MState.traceRight_right_assoc']
  linarith

/-- The quantum conditional mutual information `QCMI` is nonnegative. -/
theorem qcmi_nonneg (ρ : MState (dA × dB × dC)) :
    0 ≤ qcmi ρ := by
  simp [qcmi, qConditionalEnt]
  have := Sᵥₙ_strong_subadditivity ρ
  linarith

/-- The quantum conditional mutual information `QCMI ρABC` is at most 2 log dA. -/
theorem qcmi_le_2_log_dim (ρ : MState (dA × dB × dC)) :
    qcmi ρ ≤ 2 * Real.log (Fintype.card dA) := by
  sorry

/-- The quantum conditional mutual information `QCMI ρABC` is at most 2 log dC. -/
theorem qcmi_le_2_log_dim' (ρ : MState (dA × dB × dC)) :
    qcmi ρ ≤ 2 * Real.log (Fintype.card dC) := by
  sorry

/-- The chain rule for quantum conditional mutual information:
`I(A₁A₂ : C | B) = I(A₁:C|B) + I(A₂:C|BA₁)`.
-/
theorem qcmi_chain_rule (ρ : MState ((dA₁ × dA₂) × dB × dC)) :
    let ρA₁BC := ρ.assoc.SWAP.assoc.traceLeft.SWAP;
    let ρA₂BA₁C : MState (dA₂ × (dA₁ × dB) × dC) :=
      ((CPTPMap.id ⊗ CPTPMap.assoc').compose (CPTPMap.assoc.compose (CPTPMap.SWAP ⊗ CPTPMap.id))) ρ;
    qcmi ρ = qcmi ρA₁BC + qcmi ρA₂BA₁C
     := by
  sorry

end entropy
