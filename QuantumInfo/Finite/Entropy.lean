import QuantumInfo.Finite.Braket
import QuantumInfo.Finite.CPTPMap
import ClassicalInfo.Entropy

/-!
Quantum notions of information and entropy.

We start with quantities of _entropy_, namely the von Neumann entropy and its derived quantities:
 * Quantum conditional entropy, `qConditionalEnt`
 * Quantum mutual information, `qMutualInfo`
 * Coherent information, `coherentInfo`
 * Quantum conditional mutual information, `qcmi`.
and then prove facts about them.

The second half of the file is quantities of _relative entropy_, namely the (standard) quantum relative
entropy, and generalizations.
-/

/- # TODO / Goals:

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
-/

noncomputable section

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]
variable {dA dB dC dA₁ dA₂ : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂]

section entropy

/-- Von Neumann entropy of a mixed state. -/
def Sᵥₙ (ρ : MState d) : ℝ :=
  Hₛ (ρ.spectrum)

/-- The Quantum Conditional Entropy S(ρᴬ|ρᴮ) is given by S(ρᴬᴮ) - S(ρᴮ). -/
def qConditionalEnt (ρ : MState (dA × dB)) : ℝ :=
  Sᵥₙ ρ - Sᵥₙ ρ.traceLeft

/-- The Quantum Mutual Information I(A:B) is given by S(ρᴬ) + S(ρᴮ) - S(ρᴬᴮ). -/
def qMutualInfo (ρ : MState (dA × dB)) : ℝ :=
  Sᵥₙ ρ.traceLeft + Sᵥₙ ρ.traceRight - Sᵥₙ ρ

/-- The Quantum Conditional Mutual Information, I(A;C|B) = S(A|B) - S(A|BC). -/
def qcmi (ρ : MState (dA × dB × dC)) : ℝ :=
  qConditionalEnt ρ.assoc'.traceRight - qConditionalEnt ρ

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

end entropy

section relative_entropy

/-!
To do relative entropies, we start with the _sandwiched Renyi Relative Entropy_ which is a nice general form.
Then instead of proving many theorems (like DPI, relabelling, additivity, etc.) several times, we just prove
it for this one quantity, then it follows for other quantities (like the relative entropy) as a special case.

We could even imagine restructuring the file so that relative entropy comes first, then (some) properties
about other quantities can be derived, since they can pretty much all be expressed in terms of appropriate
special cases of relative entropies.
-/

/-- The Sandwiched Renyi Relative Entropy, defined with ln (nits). Note that at `α = 1` this definition
  switch to the standard Relative Entropy, for continuity. -/
def SandwichedRelRentropy [Fintype d] (α : ℝ) (ρ σ : MState d) : ENNReal :=
  open ComplexOrder Classical in
  if σ.M.ker ≤ ρ.M.ker
  then (.ofNNReal ⟨
    if α = 1 then
      ρ.M.inner (HermitianMat.log ρ - HermitianMat.log σ)
    else
      ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).toMat) ^ α).trace.log / (α - 1)
    , by
      --Proof that this quantity is nonnegative
      sorry
     ⟩)
  else ⊤

notation "D̃_" α "(" ρ "‖" σ ")" => SandwichedRelRentropy α ρ σ

/-- The Sandwiched Renyi Relative entropy is additive when the inputs are product states -/
@[simp]
theorem sandwichedRelRentropy_additive (α) (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    D̃_ α(ρ₁ ⊗ ρ₂‖σ₁ ⊗ σ₂) = D̃_ α(ρ₁‖σ₁) + D̃_ α(ρ₂‖σ₂) := by
  dsimp [SandwichedRelRentropy]
  sorry
  -- split_ifs
  /-
  handle the kernels of tensor products
  log of ⊗ is (log A ⊗ I) + (I ⊗ log B)
  rinner distributes over sub and add
  rinner of ⊗ is mul of rinner
  -/

@[simp]
theorem sandwichedRelRentropy_relabel {α : ℝ} (ρ σ : MState d) (e : d₂ ≃ d) :
    D̃_ α(ρ.relabel e‖σ.relabel e) = D̃_ α(ρ‖σ) := by
  simp only [SandwichedRelRentropy, MState.relabel_M]
  rw [HermitianMat.ker_reindex_le_iff] --Why doesn't this `simp`? Because it's an if condition, I'm guessing
  simp

@[simp]
theorem sandwichedRelRentropy_self {d : Type*} [Fintype d] [DecidableEq d] {α : ℝ}
    (hα : 0 < α) (ρ : MState d) :
  --Technically this holds for all α except for `-1` and `0`. But those are stupid.
  --TODO: Maybe SandwichedRelRentropy should actually be defined differently for α = 0?
    D̃_ α(ρ‖ρ) = 0 := by
  simp? [SandwichedRelRentropy, NNReal.eq_iff] says
    simp only [SandwichedRelRentropy, le_refl, ↓reduceIte, sub_self, HermitianMat.inner_zero,
    ENNReal.coe_eq_zero, NNReal.eq_iff, NNReal.coe_mk, NNReal.coe_zero, ite_eq_left_iff,
    div_eq_zero_iff, Real.log_eq_zero]
  intro hα
  left; right; left
  rw [HermitianMat.pow_eq_cfc, HermitianMat.pow_eq_cfc]
  nth_rw 1 [← HermitianMat.cfc_id ρ.M]
  rw [HermitianMat.cfc_conj, ← HermitianMat.cfc_comp]
  conv =>
    enter [1, 1]
    equals ρ.M.cfc id =>
      apply HermitianMat.cfc_congr_of_zero_le ρ.zero_le
      intro i (hi : 0 ≤ i)
      simp
      rw [← Real.rpow_mul_natCast hi, ← Real.rpow_one_add' hi]
      · rw [← Real.rpow_mul hi]
        field_simp
        ring_nf
        exact Real.rpow_one i
      · field_simp; ring_nf; positivity
  simp

open ComplexOrder in
@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem sandwichedRelEntropy_ne_top {α : ℝ} {d : Type*} [Fintype d] [DecidableEq d] {ρ σ : MState d}
    (hσ : σ.m.PosDef) : D̃_ α(ρ‖σ) ≠ ⊤ := by
  have h : σ.M.ker = ⊥ := hσ.toLin_ker_eq_bot
  simp [SandwichedRelRentropy, h]

@[fun_prop]
theorem sandwichedRelRentropy.continuousOn {d : Type*} [Fintype d] [DecidableEq d] (ρ σ : MState d) :
    ContinuousOn (fun α => D̃_ α(ρ‖σ)) (Set.Ioi 0) := by
  --If this turns out too hard, we just need `ContinousAt f 1`.
  --If that's still too hard, we really _just_ need that `(𝓝[≠] 1).tendsto f (f 1)`.
  sorry

/-- The Data Processing Inequality for the Sandwiched Renyi relative entropy.
Proved in `https://arxiv.org/pdf/1306.5920`. Seems kind of involved. -/
theorem sandwichedRenyiEntropy_DPI {d d₂ : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]
    {α : ℝ} (hα : 1 ≤ α) (ρ σ : MState d) (Φ : CPTPMap d d₂) : D̃_ α(Φ ρ‖Φ σ) ≤ D̃_ α(ρ‖σ) := by
  --If we want, we can prove this just for 1 < α, and then use continuity (above) to take the limit as
  -- α → 1.
  sorry

open Classical in
/-- The quantum relative entropy `𝐃(ρ‖σ) := Tr[ρ (log ρ - log σ)]`. -/
def qRelativeEnt (ρ σ : MState d) : ENNReal :=
  D̃_1(ρ‖σ)

notation "𝐃(" ρ "‖" σ ")" => qRelativeEnt ρ σ

/-- Quantum relative entropy as `Tr[ρ (log ρ - log σ)]` when supports are correct. -/
theorem qRelativeEnt_ker {ρ σ : MState d} (h : σ.M.ker ≤ ρ.M.ker) :
    𝐃(ρ‖σ).toEReal = ρ.M.inner (HermitianMat.log ρ - HermitianMat.log σ) := by
  simp [qRelativeEnt, SandwichedRelRentropy, h, EReal.coe_nnreal_eq_coe_real]

/-- The quantum relative entropy is unchanged by `MState.relabel` -/
@[simp]
theorem qRelativeEnt_relabel (ρ σ : MState d) (e : d₂ ≃ d) :
    𝐃(ρ.relabel e‖σ.relabel e) = 𝐃(ρ‖σ) := by
  simp [qRelativeEnt]

/-- "Formula for conversion from operator inequality to quantum relative entropy",
-- Proposition S17 of https://arxiv.org/pdf/2401.01926v2 -/
theorem qRelativeEnt_op_le {ρ σ : MState d} {α : ℝ} (hpos : 0 < α) (h : ρ.M ≤ α • σ.M) :
    𝐃(ρ‖σ) ≤ ENNReal.ofReal (Real.log α) := by
  sorry

@[gcongr]
theorem qRelEntropy_heq_congr {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂) (hρ : ρ₁ ≍ ρ₂) (hσ : σ₁ ≍ σ₂) :
    𝐃(ρ₁‖σ₁) = 𝐃(ρ₂‖σ₂) := by
  rw [heq_iff_exists_eq_cast] at hρ hσ
  obtain ⟨_, rfl⟩ := hρ
  obtain ⟨_, rfl⟩ := hσ
  simp [← MState.relabel_cast _ hd]

/-- Quantum relative entropy when σ has full rank -/
theorem qRelativeEnt_rank {ρ σ : MState d} (h : σ.M.ker = ⊥) :
    (𝐃(ρ‖σ) : EReal) = ρ.M.inner (HermitianMat.log ρ - HermitianMat.log σ) := by
  apply qRelativeEnt_ker
  simp only [h, bot_le]

/-- The quantum relative entropy is additive when the inputs are product states -/
@[simp]
theorem qRelativeEnt_additive (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    𝐃(ρ₁ ⊗ ρ₂‖σ₁ ⊗ σ₂) = 𝐃(ρ₁‖σ₁) + 𝐃(ρ₂‖σ₂) := by
  simp [qRelativeEnt]

/-- Relative entropy is lower semicontinuous (in each argument, actually, but we only need in the
latter here). Will need the fact that all the cfc / eigenvalue stuff is continuous, plus
carefully handling what happens with the kernel subspace, which will make this a pain. -/
@[fun_prop]
theorem qRelativeEnt.LowerSemicontinuous (ρ : MState d) : LowerSemicontinuous fun σ => 𝐃(ρ‖σ) := by
  sorry

@[simp]
theorem qRelEntropy_self {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) :
    𝐃(ρ‖ρ) = 0 := by
  simp [qRelativeEnt]

open ComplexOrder in
@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem qRelativeEnt_ne_top {d : Type*} [Fintype d] [DecidableEq d] {ρ σ : MState d}
    (hσ : σ.m.PosDef) : 𝐃(ρ‖σ) ≠ ⊤ := by
  rw [qRelativeEnt]
  finiteness

end relative_entropy
