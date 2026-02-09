/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
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

variable {𝕜 : Type*} [RCLike 𝕜]

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

/-- The Coherent Information of a state ρ pasing through a channel Λ is the negative conditional
  entropy of the image under Λ of the purification of ρ. -/
def coherentInfo (ρ : MState d₁) (Λ : CPTPMap d₁ d₂) : ℝ :=
  let ρPure : MState (d₁ × d₁) := MState.pure ρ.purify
  let ρImg : MState (d₂ × d₁) := Λ.prod (CPTPMap.id (dIn := d₁)) ρPure
  (- qConditionalEnt ρImg)

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

/-- von Neumann entropy is unchanged under SWAP. TODO: All unitaries-/
@[simp]
theorem Sᵥₙ_of_SWAP_eq (ρ : MState (d₁ × d₂)) : Sᵥₙ ρ.SWAP = Sᵥₙ ρ := by
  apply Hₛ_eq_of_multiset_map_eq
  exact ρ.multiset_spectrum_relabel_eq (Equiv.prodComm d₁ d₂).symm

/-- von Neumann entropy is unchanged under assoc. -/
@[simp]
theorem Sᵥₙ_of_assoc_eq (ρ : MState ((d₁ × d₂) × d₃)) : Sᵥₙ ρ.assoc = Sᵥₙ ρ := by
  apply Hₛ_eq_of_multiset_map_eq
  apply ρ.multiset_spectrum_relabel_eq

/-- von Neumann entropy is unchanged under assoc'. -/
@[simp]
theorem Sᵥₙ_of_assoc'_eq (ρ : MState (d₁ × (d₂ × d₃))) : Sᵥₙ ρ.assoc' = Sᵥₙ ρ := by
  rw [← Sᵥₙ_of_assoc_eq, ρ.assoc_assoc']

--PULLOUT
theorem HermitianMat.trace_mul_cfc (A : HermitianMat d 𝕜) (f : ℝ → ℝ) :
    (A.toMat * (A.cfc f).toMat).trace = ∑ i, A.H.eigenvalues i * f (A.H.eigenvalues i) := by
  conv_lhs => rw [A.eq_conj_diagonal]
  rw [cfc_conj_unitary]
  simp [conj, Matrix.mul_assoc, A.H.eigenvectorUnitary.val.trace_mul_comm]
  simp [← Matrix.mul_assoc, Matrix.IsHermitian.eigenvectorUnitary ]

omit [DecidableEq dA] in
open scoped Kronecker in
/--
`Tr(M (A ⊗ I)) = Tr(Tr_B(M) A)`
-/
theorem Matrix.trace_mul_kron_one_right {R : Type*} [Ring R]
    (M : Matrix (dA × dB) (dA × dB) R) (A : Matrix dA dA R) :
    (M * (A ⊗ₖ (1 : Matrix dB dB R))).trace = (M.traceRight * A).trace := by
  simp [trace, mul_apply, kroneckerMap_apply, traceRight, one_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

omit [DecidableEq dB] in
open scoped Kronecker in
/--
`Tr(M (I ⊗ B)) = Tr(Tr_A(M) B)`
-/
theorem Matrix.trace_mul_one_kron_right {R : Type*} [Ring R]
    (M : Matrix (dA × dB) (dA × dB) R) (B : Matrix dB dB R) :
    (M * ((1 : Matrix dA dA R) ⊗ₖ B)).trace = (M.traceLeft * B).trace := by
  simp [trace, mul_apply, kroneckerMap_apply, traceLeft, one_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

open ComplexOrder in
theorem HermitianMat.inner_log_smul_of_posDef
    {ρ σ : HermitianMat d 𝕜} (hσ : σ.toMat.PosDef)
    {x : ℝ} (hx : x ≠ 0) :
    ρ.inner (x • σ).log = Real.log x * ρ.trace + ρ.inner σ.log := by
  have h_log_smul : (x • σ).log = Real.log x • 1 + σ.log := by
    convert HermitianMat.log_smul hx hσ using 1;
  simp [ h_log_smul, HermitianMat.inner, mul_add, Matrix.trace_smul, RCLike.smul_re ]
  exact Or.inl rfl

theorem Sᵥₙ_eq_neg_trace_log (ρ : MState d) : Sᵥₙ ρ = - ρ.M.inner (ρ.M.log) := by
  open HermitianMat in
  rw [log, inner_eq_re_trace]
  nth_rw 1 [← cfc_id ρ.M]
  rw [← coe_cfc_mul]
  simp only [Sᵥₙ, Hₛ, H₁, Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_inj]
  rw [← trace_eq_re_trace, ← sum_eigenvalues_eq_trace]
  obtain ⟨e, he⟩ := ρ.M.cfc_eigenvalues (id * Real.log)
  apply Finset.sum_equiv e.symm (by simp)
  simp [MState.spectrum, Distribution.mk', he]

/-- von Neumman entropies of the left- and right- partial trace of pure states are equal. -/
theorem Sᵥₙ_of_partial_eq (ψ : Ket (d₁ × d₂)) :
    Sᵥₙ (MState.pure ψ).traceLeft = Sᵥₙ (MState.pure ψ).traceRight := by
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

/-- "Ordinary" subadditivity of von Neumann entropy -/
theorem Sᵥₙ_subadditivity (ρ : MState (d₁ × d₂)) :
    Sᵥₙ ρ ≤ Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft := by
  sorry

/--
The purity of a state is invariant under relabeling of the basis.
-/
@[simp]
theorem purity_relabel (ρ : MState d₁) (e : d₂ ≃ d₁) : (ρ.relabel e).purity = ρ.purity := by
  simp [MState.purity, MState.inner]

/-
Relabeling a pure state by a bijection yields another pure state.
-/
theorem relabel_pure_exists (ψ : Ket d₁) (e : d₂ ≃ d₁) :
    ∃ ψ' : Ket d₂, (MState.pure ψ).relabel e = MState.pure ψ' := by
  refine ⟨⟨fun i => ψ (e i), ?_⟩, rfl⟩
  rw [← ψ.normalized', Fintype.sum_equiv e]
  congr!

/--
Triangle inequality for pure tripartite states: S(A) ≤ S(B) + S(C).
-/
private theorem Sᵥₙ_pure_tripartite_triangle {d₁ d₂ d₃ : Type*} [Fintype d₁] [Fintype d₂] [Fintype d₃]
    [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃] (ψ : Ket ((d₁ × d₂) × d₃)) :
    Sᵥₙ (MState.pure ψ).traceRight.traceRight ≤
    Sᵥₙ (MState.pure ψ).traceRight.traceLeft + Sᵥₙ (MState.pure ψ).traceLeft := by
  have h_subadd : Sᵥₙ ((MState.pure ψ).assoc.traceLeft) ≤ Sᵥₙ ((MState.pure ψ).assoc.traceLeft.traceRight) + Sᵥₙ ((MState.pure ψ).assoc.traceLeft.traceLeft) := by
    apply Sᵥₙ_subadditivity;
  obtain ⟨ψ', hψ'⟩ : ∃ ψ', (MState.pure ψ).assoc = MState.pure ψ' :=
    relabel_pure_exists ψ (Equiv.prodAssoc d₁ d₂ d₃).symm
  grind [Sᵥₙ_of_partial_eq, MState.traceLeft_left_assoc, MState.traceLeft_right_assoc, MState.traceRight_assoc]

/--
One direction of the Araki-Lieb triangle inequality: S(A) ≤ S(B) + S(AB).
-/
theorem Sᵥₙ_triangle_ineq_one_way (ρ : MState (d₁ × d₂)) : Sᵥₙ ρ.traceRight ≤ Sᵥₙ ρ.traceLeft + Sᵥₙ ρ := by
  have := Sᵥₙ_pure_tripartite_triangle (ρ.purify)
  have := Sᵥₙ_of_partial_eq ρ.purify
  aesop

/-- Araki-Lieb triangle inequality on von Neumann entropy -/
theorem Sᵥₙ_triangle_subaddivity (ρ : MState (d₁ × d₂)) :
    abs (Sᵥₙ ρ.traceRight - Sᵥₙ ρ.traceLeft) ≤ Sᵥₙ ρ := by
  rw [abs_sub_le_iff]
  constructor
  · have := Sᵥₙ_triangle_ineq_one_way ρ
    grind only
  · have := Sᵥₙ_triangle_ineq_one_way ρ.SWAP
    grind only [Sᵥₙ_triangle_ineq_one_way, Sᵥₙ_of_SWAP_eq, MState.traceRight_SWAP,
      MState.traceLeft_SWAP]

/-- Strong subadditivity on a tripartite system -/
theorem Sᵥₙ_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    let ρ₁₂ := ρ₁₂₃.assoc'.traceRight;
    let ρ₂₃ := ρ₁₂₃.traceLeft;
    let ρ₂ := ρ₁₂₃.traceLeft.traceRight;
    Sᵥₙ ρ₁₂₃ + Sᵥₙ ρ₂ ≤ Sᵥₙ ρ₁₂ + Sᵥₙ ρ₂₃ := by
  sorry

/-- Weak monotonicity of quantum conditional entropy. S(A|B) + S(A|C) ≥ 0 -/
theorem Sᵥₙ_weak_monotonicity (ρ : MState (dA × dB × dC)) :
    let ρAB := ρ.assoc'.traceRight
    let ρAC := ρ.SWAP.assoc.traceLeft.SWAP
    0 ≤ qConditionalEnt ρAB + qConditionalEnt ρAC := by
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
  have := Sᵥₙ_subadditivity ρ.assoc'.traceRight
  have := abs_le.mp (Sᵥₙ_triangle_subaddivity ρ)
  grind [qcmi, qConditionalEnt, Sᵥₙ_nonneg, Sᵥₙ_le_log_d]

/-- The quantum conditional mutual information `QCMI ρABC` is at most 2 log dC. -/
theorem qcmi_le_2_log_dim' (ρ : MState (dA × dB × dC)) :
    qcmi ρ ≤ 2 * Real.log (Fintype.card dC) := by
  have h_araki_lieb_assoc' : Sᵥₙ ρ.assoc'.traceRight - Sᵥₙ ρ.traceLeft.traceLeft ≤ Sᵥₙ ρ := by
    apply le_of_abs_le
    rw [← ρ.traceLeft_assoc', ← Sᵥₙ_of_assoc'_eq ρ]
    exact Sᵥₙ_triangle_subaddivity ρ.assoc'
  have := Sᵥₙ_subadditivity ρ.traceLeft
  grind [qcmi, qConditionalEnt, Sᵥₙ_le_log_d, MState.traceRight_left_assoc']

-- /-- The chain rule for quantum conditional mutual information:
-- `I(A₁A₂ : C | B) = I(A₁:C|B) + I(A₂:C|BA₁)`.
-- -/
-- theorem qcmi_chain_rule (ρ : MState ((dA₁ × dA₂) × dB × dC)) :
--     let ρA₁BC := ρ.assoc.SWAP.assoc.traceLeft.SWAP;
--     let ρA₂BA₁C : MState (dA₂ × (dA₁ × dB) × dC) :=
--       ((CPTPMap.id ⊗ₖ CPTPMap.assoc').compose (CPTPMap.assoc.compose (CPTPMap.SWAP ⊗ₖ CPTPMap.id))) ρ;
--     qcmi ρ = qcmi ρA₁BC + qcmi ρA₂BA₁C
--      := by
--   sorry

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

theorem inner_log_sub_log_nonneg (ρ σ : MState d) (h : σ.M.ker ≤ ρ.M.ker) :
    0 ≤ ρ.M.inner (ρ.M.log - σ.M.log) := by
  sorry

theorem sandwichedRelRentropy_nonneg (α : ℝ) (ρ σ : MState d) (h : σ.M.ker ≤ ρ.M.ker) :
    0 ≤ if α = 1 then ρ.M.inner (ρ.M.log - σ.M.log)
      else ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).toMat) ^ α).trace.log / (α - 1) := by
  split_ifs
  · exact inner_log_sub_log_nonneg ρ σ h
  sorry

/-- The Sandwiched Renyi Relative Entropy, defined with ln (nits). Note that at `α = 1` this definition
  switch to the standard Relative Entropy, for continuity. -/
def SandwichedRelRentropy [Fintype d] (α : ℝ) (ρ σ : MState d) : ENNReal :=
  open Classical in
  if h : σ.M.ker ≤ ρ.M.ker
  then (.ofNNReal ⟨if α = 1 then
      ρ.M.inner (HermitianMat.log ρ - HermitianMat.log σ)
    else
      ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).toMat) ^ α).trace.log / (α - 1),
    by exact sandwichedRelRentropy_nonneg α ρ σ h  ⟩)
  else ⊤

notation "D̃_" α "(" ρ "‖" σ ")" => SandwichedRelRentropy α ρ σ

/-- The Sandwiched Renyi Relative entropy is additive when the inputs are product states -/
@[simp]
theorem sandwichedRelRentropy_additive (α) (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    D̃_ α(ρ₁ ⊗ ρ₂‖σ₁ ⊗ σ₂) = D̃_ α(ρ₁‖σ₁) + D̃_ α(ρ₂‖σ₂) := by
  dsimp [SandwichedRelRentropy]
  sorry
  -- split_ifs
  -- · sorry
  -- · sorry
  -- · sorry
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
  rw! [HermitianMat.ker_reindex_le_iff] --Why doesn't this `simp`? Because it's an if condition, I'm guessing
  simp

@[simp]
theorem sandwichedRelRentropy_self {d : Type*} [Fintype d] [DecidableEq d] {α : ℝ}
    (hα : 0 < α) (ρ : MState d) :
  --Technically this holds for all α except for `-1` and `0`. But those are stupid.
  --TODO: Maybe SandwichedRelRentropy should actually be defined differently for α = 0?
    D̃_ α(ρ‖ρ) = 0 := by
  simp? [SandwichedRelRentropy, NNReal.eq_iff] says
    simp only [SandwichedRelRentropy, le_refl, ↓reduceDIte, sub_self, HermitianMat.inner_zero,
    ENNReal.coe_eq_zero, NNReal.eq_iff, NNReal.coe_mk, NNReal.coe_zero, ite_eq_left_iff,
    div_eq_zero_iff, Real.log_eq_zero]
  intro hα
  left; right; left
  rw [HermitianMat.pow_eq_cfc, HermitianMat.pow_eq_cfc]
  nth_rw 2 [← HermitianMat.cfc_id ρ.M]
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

--PULLOUT
@[simp]
theorem HermitianMat.ker_smul (ρ : HermitianMat d 𝕜) {α : ℝ} (hα : α ≠ 0) :
    (α • ρ).ker = ρ.ker := by
  ext
  simp only [ker, lin]
  simp [Matrix.toEuclideanLin, funext_iff, Matrix.mulVec,
    RCLike.real_smul_eq_coe_mul, dotProduct, mul_assoc, ← Finset.mul_sum, hα]

theorem HermitianMat.ker_le_of_le_smul {ρ σ : HermitianMat d 𝕜} {α : ℝ} (hα : α ≠ 0) (hρ : 0 ≤ ρ)
    (h : ρ ≤ α • σ) : σ.ker ≤ ρ.ker := by
  rw [← ker_smul σ hα]
  exact ker_antitone hρ h

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

--BACKPORT
private theorem lowerSemicontinuous_iff {α : Type u_1} {β : Type u_2} [TopologicalSpace α] [Preorder β] {f : α → β} :
    LowerSemicontinuous f ↔ ∀ (x : α), LowerSemicontinuousAt f x := by
  rfl

lemma lowerSemicontinuous_inner (ρ x : MState d) (hx : x.M.ker ≤ ρ.M.ker):
    LowerSemicontinuousAt (fun x ↦ ρ.M.inner (ρ.M.log - x.M.log)) x := by
  sorry

open Classical in
theorem qRelativeEnt_lowerSemicontinuous_2 (ρ x : MState d) (hx : ¬(x.M.ker ≤ ρ.M.ker)) (y : ENNReal) (hy : y < ⊤) :
    ∀ᶠ (x' : MState d) in nhds x,
      y < (if x'.M.ker ≤ ρ.M.ker then ρ.M.inner (ρ.M.log - x'.M.log) else ⊤ : EReal) := by
  sorry

/-- Relative entropy is lower semicontinuous (in each argument, actually, but we only need in the
latter here). Will need the fact that all the cfc / eigenvalue stuff is continuous, plus
carefully handling what happens with the kernel subspace, which will make this a pain. -/
@[fun_prop]
theorem qRelativeEnt.lowerSemicontinuous (ρ : MState d) : LowerSemicontinuous fun σ => 𝐃(ρ‖σ) := by
  simp_rw [qRelativeEnt, SandwichedRelRentropy, if_true, lowerSemicontinuous_iff]
  intro x
  by_cases hx : x.M.ker ≤ ρ.M.ker
  · have h₂ := lowerSemicontinuous_inner ρ x hx
    sorry
  · intro y hy
    simp only [hx, ↓reduceDIte] at hy ⊢
    have h₂ := qRelativeEnt_lowerSemicontinuous_2 ρ x hx y hy
    sorry

/-- Joint convexity of Quantum relative entropy. We can't state this with `ConvexOn` because that requires
an `AddCommMonoid`, which `MState`s are not. Instead we state it with `Mixable`.

TODO:
 * Add the `Mixable` instance that infers from the `Coe` so that the right hand side can be written as
`p [𝐃(ρ₁‖σ₁) ↔ 𝐃(ρ₂‖σ₂)]`
 * Define (joint) convexity as its own thing - a `ConvexOn` for `Mixable` types.
 * Maybe, more broadly, find a way to make `ConvexOn` work with the subset of `Matrix` that corresponds to `MState`.
-/
theorem qRelativeEnt_joint_convexity :
  ∀ (ρ₁ ρ₂ σ₁ σ₂ : MState d), ∀ (p : Prob),
    𝐃(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂]) ≤ p * 𝐃(ρ₁‖σ₁) + (1 - p) * 𝐃(ρ₂‖σ₂) := by
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

/-- `I(A:B) = 𝐃(ρᴬᴮ‖ρᴬ ⊗ ρᴮ)` -/
theorem qMutualInfo_as_qRelativeEnt (ρ : MState (dA × dB)) :
    qMutualInfo ρ = (𝐃(ρ‖ρ.traceRight ⊗ ρ.traceLeft) : EReal) :=
  sorry

theorem qRelEntropy_le_add_of_le_smul {d : Type*} [Fintype d] [DecidableEq d]
  (ρ : MState d) {σ₁ σ₂ : MState d} (r : ℝ) (hσ : σ₁.M ≤ r • σ₂.M) :
    𝐃(ρ‖σ₁) ≤ 𝐃(ρ‖σ₂) + ENNReal.ofReal (Real.log r)
    := by
  sorry

end relative_entropy
