import QuantumInfo.Finite.Braket
import QuantumInfo.Finite.CPTPMap
import ClassicalInfo.Entropy

/-!
Quantum notions of information and entropy.
-/

noncomputable section

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d₁] [DecidableEq d₂]
variable {dA dB dC dA₁ dA₂ : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂]

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
def qRelativeEnt (ρ σ : MState d) : ENNReal :=
  (if
    LinearMap.ker σ.val.toLin' ≤ LinearMap.ker ρ.val.toLin'
  then
    some ⟨ρ.M.inner (HermitianMat.log ρ - HermitianMat.log σ),
    /- Quantum relative entropy is nonnegative. This can be proved by an application of
    Klein's inequality. -/
    sorry⟩
  else
    ⊤)

notation "𝐃(" ρ "‖" σ ")" => qRelativeEnt ρ σ

/-- Quantum relative entropy as `Tr[ρ (log ρ - log σ)]` when supports are correct. -/
theorem qRelativeEnt_ker {ρ σ : MState d} (h : LinearMap.ker σ.val.toLin' ≤ LinearMap.ker ρ.val.toLin') :
    (𝐃(ρ‖σ) : EReal) = ρ.M.inner (HermitianMat.log ρ - HermitianMat.log σ) := by
  simp only [qRelativeEnt, h]
  congr

/-- The quantum relative entropy is unchanged by `MState.relabel` -/
@[simp]
theorem qRelativeEnt_relabel (ρ σ : MState d) (e : d₂ ≃ d) :
    𝐃(ρ.relabel e‖σ.relabel e) = 𝐃(ρ‖σ) := by
  unfold qRelativeEnt
  split_ifs with h₁ h₂ h₂
  · congr 2
    simp only [HermitianMat.inner, MState.relabel_m, RCLike.re_to_complex]
    congr 1
    --Push relabels through matrix log
    --Use the fact that Matrix.trace (m.submatrix ⇑e ⇑e) = Matrix.trace m
    sorry
  rotate_right
  · rfl
  --The rest of this is about kernels of linear maps under equivs. Probably belongs elsewhere
  all_goals
    dsimp [MState.relabel] at h₁
    sorry
    -- simp only [Matrix.toLin'_submatrix] at h₁
    -- have hbot : LinearMap.ker (LinearMap.funLeft ℂ ℂ ⇑e) = ⊥ := by
    --   apply LinearMap.ker_eq_bot_of_inverse
    --   rw [← LinearMap.funLeft_comp, Equiv.self_comp_symm]
    --   rfl
    -- rw [LinearMap.ker_comp_of_ker_eq_bot _ hbot, LinearMap.ker_comp] at h₁
    -- rw [LinearMap.ker_comp_of_ker_eq_bot _ hbot, LinearMap.ker_comp] at h₁
  -- case neg =>
  --   apply h₂
  --   have hsurj : Function.Surjective ⇑(LinearMap.funLeft ℂ ℂ ⇑e.symm) :=
  --     LinearMap.funLeft_surjective_of_injective _ _ _ e.symm.injective
  --   replace h₁ := Submodule.map_mono h₁ (f := LinearMap.funLeft ℂ ℂ ⇑e.symm)
  --   rw [Submodule.map_comap_eq_of_surjective hsurj] at h₁
  --   rw [Submodule.map_comap_eq_of_surjective hsurj] at h₁
  --   exact h₁
  -- case pos =>
  --   exact h₁ (Submodule.comap_mono h₂)

/-- The Quantum Conditional Mutual Information, I(A;C|B) = S(A|B) - S(A|BC). -/
def qcmi (ρ : MState (dA × dB × dC)) : ℝ :=
  qConditionalEnt ρ.assoc'.traceRight - qConditionalEnt ρ

open ComplexOrder in
open Classical in
/-- The Sandwiched Renyi Relative Entropy, defined with ln (nits). Note that at `α = 1` this definition
  switch to the standard Relative Entropy, for continuity. -/
def SandwichedRelRentropy [Fintype d] (α : ℝ) (ρ σ : MState d) : ENNReal :=
  if
    LinearMap.ker σ.val.toLin' ≤ LinearMap.ker ρ.val.toLin'
  then (
    if α = 1 then
      𝐃(ρ‖σ)
    else
      .ofNNReal ⟨
        ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).toMat) ^ α).trace.log / (α - 1)
      , by
        --Proof that this quantity is nonnegative
        sorry
          ⟩)
  else ⊤

notation "D̃_ " α "(" ρ "‖" σ ")" => SandwichedRelRentropy α ρ σ

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


/-- Quantum relative entropy when σ has full rank -/
theorem qRelativeEnt_rank {ρ σ : MState d} (h : LinearMap.ker σ.val.toLin' = ⊥) :
    (𝐃(ρ‖σ) : EReal) = ρ.M.inner (HermitianMat.log ρ - HermitianMat.log σ) := by
  apply qRelativeEnt_ker
  simp only [h, bot_le]

/-- The quantum relative entropy is additive when the inputs are product states -/
theorem qRelativeEnt_additive (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    𝐃(ρ₁ ⊗ ρ₂‖σ₁ ⊗ σ₂) = 𝐃(ρ₁‖σ₁) + 𝐃(ρ₂‖σ₂) := by
  --handle the kernels of tensor products
  --log of ⊗ is (log A ⊗ I) + (I ⊗ log B)
  --rinner distributes over sub and add
  --rinner of ⊗ is mul of rinner
  sorry

/-- Relative entropy is continuous (in each argument, actually, but we only need in the
latter here). Will need the fact that all the cfc / eigenvalue stuff is continuous, which
is going to make this a pain. -/
@[fun_prop]
theorem qRelativeEnt.Continuous (ρ : MState d) : Continuous fun σ => 𝐃(ρ‖σ) := by
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
    𝐃(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂]) ≤ p * 𝐃(ρ₁‖σ₁) + (1 - p) * 𝐃(ρ₂‖σ₂) := by
  sorry

omit [DecidableEq d]

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

/-- The Sandwiched Renyi Relative entropy is additive when the inputs are product states -/
theorem SandwichedRelRentropy_additive (α) (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    D̃_ α(ρ₁ ⊗ ρ₂‖σ₁ ⊗ σ₂) = D̃_ α(ρ₁‖σ₁) + D̃_ α(ρ₂‖σ₂) := by
  dsimp [SandwichedRelRentropy]
  sorry
  -- split_ifs
  -- · sorry
  -- · sorry
  -- · sorry

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
    qMutualInfo ρ = (𝐃(ρ‖ρ.traceRight ⊗ ρ.traceLeft) : EReal) :=
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
      ((CPTPMap.id ⊗ₖ CPTPMap.assoc').compose (CPTPMap.assoc.compose (CPTPMap.SWAP ⊗ₖ CPTPMap.id))) ρ;
    qcmi ρ = qcmi ρA₁BC + qcmi ρA₂BA₁C
     := by
  sorry

end entropy
