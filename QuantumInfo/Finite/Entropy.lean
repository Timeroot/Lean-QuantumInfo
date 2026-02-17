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
variable {α : ℝ}

open scoped InnerProductSpace RealInnerProductSpace

section entropy

/-- Von Neumann entropy of a mixed state. -/
def Sᵥₙ (ρ : MState d) : ℝ :=
  Hₛ ρ.spectrum

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

theorem Sᵥₙ_eq_neg_trace_log (ρ : MState d) : Sᵥₙ ρ = - ⟪ρ.M.log, ρ.M⟫ := by
  open HermitianMat in
  rw [log, inner_eq_re_trace]
  nth_rw 2 [← cfc_id ρ.M]
  rw [← mat_cfc_mul]
  simp only [Sᵥₙ, Hₛ, H₁, Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_inj]
  rw [← trace_eq_re_trace, ← sum_eigenvalues_eq_trace]
  obtain ⟨e, he⟩ := ρ.M.cfc_eigenvalues (Real.log * id)
  apply Finset.sum_equiv e.symm (by simp)
  simp [MState.spectrum, Distribution.mk', he, mul_comm]

/-- Von Neumann entropy is invariant under relabeling of the basis. -/
@[simp]
theorem Sᵥₙ_relabel (ρ : MState d₁) (e : d₂ ≃ d₁) :
    Sᵥₙ (ρ.relabel e) = Sᵥₙ ρ := by
  simp [Sᵥₙ_eq_neg_trace_log]

/-- Von Neumann entropy is unchanged under SWAP. TODO: All unitaries-/
@[simp]
theorem Sᵥₙ_of_SWAP_eq (ρ : MState (d₁ × d₂)) : Sᵥₙ ρ.SWAP = Sᵥₙ ρ := by
  apply Hₛ_eq_of_multiset_map_eq
  exact ρ.multiset_spectrum_relabel_eq (Equiv.prodComm d₁ d₂).symm

/-- Von Neumann entropy is unchanged under assoc. -/
@[simp]
theorem Sᵥₙ_of_assoc_eq (ρ : MState ((d₁ × d₂) × d₃)) : Sᵥₙ ρ.assoc = Sᵥₙ ρ := by
  apply Hₛ_eq_of_multiset_map_eq
  apply ρ.multiset_spectrum_relabel_eq

/-- Von Neumann entropy is unchanged under assoc'. -/
@[simp]
theorem Sᵥₙ_of_assoc'_eq (ρ : MState (d₁ × (d₂ × d₃))) : Sᵥₙ ρ.assoc' = Sᵥₙ ρ := by
  rw [← Sᵥₙ_of_assoc_eq, ρ.assoc_assoc']

/-- Von Neumann entropy is the trace of the matrix function `x ↦ -x log x`. -/
theorem Sᵥₙ_eq_trace_cfc_negMulLog (ρ : MState d) :
    Sᵥₙ ρ = (ρ.M.cfc Real.negMulLog).trace := by
  open HermitianMat in
  unfold Real.negMulLog
  rw [Sᵥₙ_eq_neg_trace_log, trace, log, inner_eq_re_trace, IsMaximalSelfAdjoint.RCLike_selfadjMap]
  nth_rw 2 [← cfc_id ρ.M]
  rw [← mat_cfc_mul, RCLike.re_to_complex, ← Complex.neg_re, ← Matrix.trace_neg]
  rw [← mat_neg, ← ρ.M.cfc_neg]
  congr! 5
  simp [mul_comm]

@[fun_prop]
theorem selfAdjointMap_Continuous {𝕜 : Type*} [RCLike 𝕜] :
    Continuous (IsMaximalSelfAdjoint.selfadjMap : 𝕜 →+ ℝ) := by
  rw [IsMaximalSelfAdjoint.RCLike_selfadjMap]
  fun_prop

@[fun_prop]
theorem HermitianMat.trace_Continuous {d 𝕜 : Type*} [Fintype d] [RCLike 𝕜]  :
    Continuous (HermitianMat.trace : HermitianMat d 𝕜 → ℝ) := by
  rw [funext HermitianMat.trace_eq_re_trace]
  fun_prop

@[fun_prop]
theorem Sᵥₙ_continuous : Continuous (Sᵥₙ (d := d)) := by
  rw [funext Sᵥₙ_eq_trace_cfc_negMulLog]
  fun_prop

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

/-- The purity of a state is invariant under relabeling of the basis. -/
@[simp]
theorem purity_relabel (ρ : MState d₁) (e : d₂ ≃ d₁) : (ρ.relabel e).purity = ρ.purity := by
  simp [MState.purity, MState.inner_def]

/-- Relabeling a pure state by a bijection yields another pure state. -/
theorem relabel_pure_exists (ψ : Ket d₁) (e : d₂ ≃ d₁) :
    ∃ ψ' : Ket d₂, (MState.pure ψ).relabel e = MState.pure ψ' := by
  refine ⟨⟨fun i => ψ (e i), ?_⟩, rfl⟩
  rw [← ψ.normalized', Fintype.sum_equiv e]
  congr!

/-- For a pure state, the entropy of one subsystem equals the entropy of its complement,
even after relabeling. -/
@[simp]
theorem Sᵥₙ_pure_complement (ψ : Ket d₁) (e : d₂ × d₃ ≃ d₁) :
    Sᵥₙ ((MState.pure ψ).relabel e).traceLeft = Sᵥₙ ((MState.pure ψ).relabel e).traceRight := by
  obtain ⟨ψ', hψ'⟩ := relabel_pure_exists ψ e
  simp only [hψ', Sᵥₙ_of_partial_eq]

/-- Triangle inequality for pure tripartite states: S(A) ≤ S(B) + S(C). -/
private theorem Sᵥₙ_pure_tripartite_triangle (ψ : Ket ((d₁ × d₂) × d₃)) :
    Sᵥₙ (MState.pure ψ).traceRight.traceRight ≤
    Sᵥₙ (MState.pure ψ).traceRight.traceLeft + Sᵥₙ (MState.pure ψ).traceLeft := by
  have h_subadd := Sᵥₙ_subadditivity (MState.pure ψ).assoc.traceLeft
  obtain ⟨ψ', hψ'⟩ : ∃ ψ', (MState.pure ψ).assoc = _ :=
    relabel_pure_exists ψ _
  grind [Sᵥₙ_of_partial_eq, MState.traceLeft_left_assoc,
    MState.traceLeft_right_assoc, MState.traceRight_assoc]

/-- One direction of the Araki-Lieb triangle inequality: S(A) ≤ S(B) + S(AB). -/
theorem Sᵥₙ_triangle_ineq_one_way (ρ : MState (d₁ × d₂)) : Sᵥₙ ρ.traceRight ≤ Sᵥₙ ρ.traceLeft + Sᵥₙ ρ := by
  have := Sᵥₙ_pure_tripartite_triangle ρ.purify
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

section weak_monotonicity

variable (ρ : MState (dA × dB × dC))

/-
Permutations of the purification system for use in the proof of weak monotonicity.
-/
private def perm_B_ACR : (dA × dB × dC) × (dA × dB × dC) ≃ dB × (dA × dC × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; (b, (a,c,r))
  invFun x := let (b, (a,c,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

private def perm_C_ABR : (dA × dB × dC) × (dA × dB × dC) ≃ dC × (dA × dB × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; (c, (a,b,r))
  invFun x := let (c, (a,b,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

private def perm_AC_BR : (dA × dB × dC) × (dA × dB × dC) ≃ (dA × dC) × (dB × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; ((a,c), (b,r))
  invFun x := let ((a,c), (b,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

private def perm_AB_CR : (dA × dB × dC) × (dA × dB × dC) ≃ (dA × dB) × (dC × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; ((a,b), (c,r))
  invFun x := let ((a,b), (c,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- The state on systems A, B, and R, obtained by purifying ρ and tracing out C. -/
private def ρABR (ρ : MState (dA × dB × dC)) : MState (dA × dB × (dA × dB × dC)) :=
  ((MState.pure ρ.purify).relabel perm_C_ABR.symm).traceLeft

private lemma traceRight_relabel_perm_C_ABR
    (ρ : MState ((dA × dB × dC) × (dA × dB × dC))) :
    (ρ.relabel perm_C_ABR.symm).traceRight = ρ.traceRight.traceLeft.traceLeft := by
  ext i j;
  simp [ HermitianMat.traceRight, HermitianMat.traceLeft, perm_C_ABR ];
  simp [ Matrix.traceRight, Matrix.traceLeft ];
  simp [ Fintype.sum_prod_type ];
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ac_rfl )

private lemma trace_relabel_purify_eq_rho_C :
    ((MState.pure ρ.purify).relabel perm_C_ABR.symm).traceRight = ρ.traceLeft.traceLeft := by
  have := MState.purify_spec ρ;
  convert traceRight_relabel_perm_C_ABR _ using 1;
  rw [ this ]

private theorem S_B_eq_S_ACR (ρ : MState (dA × dB × dC)) :
    Sᵥₙ ((MState.pure ρ.purify).relabel perm_B_ACR.symm).traceRight = Sᵥₙ ρ.traceLeft.traceRight := by
  have := @MState.purify_spec;
  convert congr_arg Sᵥₙ ( this ρ |> congr_arg ( fun ρ => ρ.traceLeft.traceRight ) ) using 1;
  convert Sᵥₙ_relabel _ _ using 2;
  swap;
  exact Equiv.refl dB;
  ext; simp [ MState.traceRight, MState.traceLeft ] ;
  simp [HermitianMat.traceLeft, HermitianMat.traceRight ];
  simp [ Matrix.traceRight, Matrix.traceLeft ];
  simp [ Fintype.sum_prod_type ];
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ac_rfl )

/-
The entropy of the B marginal of the purification is equal to the entropy of the B marginal of the original state.
-/
private lemma S_B_eq_S_B :
    Sᵥₙ (ρABR ρ).traceLeft.traceRight = Sᵥₙ ρ.assoc'.traceRight.traceLeft := by
  convert S_B_eq_S_ACR ρ using 1;
  · congr 1
    ext1
    unfold ρABR;
    ext
    simp [MState.traceLeft, MState.traceRight]
    unfold perm_C_ABR perm_B_ACR
    simp [HermitianMat.traceLeft, HermitianMat.traceRight]
    simp [Matrix.traceLeft, Matrix.traceRight]
    simp [ ← Finset.sum_product']
    exact Finset.sum_bij ( fun x _ => ( x.2.1, x.2.2, x.1 ) ) ( by aesop ) ( by aesop ) ( by aesop ) ( by aesop );
  · simp

/-
The entropy of the ABR state is equal to the entropy of C, since ABCR is pure.
-/
private theorem S_ABR_eq_S_C : Sᵥₙ (ρABR ρ) = Sᵥₙ ρ.traceLeft.traceLeft := by
  rw [ρABR, Sᵥₙ_pure_complement, trace_relabel_purify_eq_rho_C]

/-
The BR marginal of ρABR is equal to the BR marginal of the purification relabeled.
-/
private lemma traceLeft_ρABR_eq_traceLeft_relabel :
    (ρABR ρ).traceLeft = ((MState.pure ρ.purify).relabel perm_AC_BR.symm).traceLeft := by
  unfold ρABR;
  unfold MState.traceLeft;
  congr;
  ext i j
  simp [ HermitianMat.traceLeft];
  simp [ Matrix.traceLeft];
  simp [ perm_C_ABR, perm_AC_BR ];
  simp [ Fintype.sum_prod_type ]

/-
Tracing out B and R from the relabeled state is equivalent to tracing out R, then B from the original state (with appropriate permutations).
-/
private lemma traceRight_relabel_perm_AC_BR (ρ : MState ((dA × dB × dC) × (dA × dB × dC))) :
    (ρ.relabel perm_AC_BR.symm).traceRight = ρ.traceRight.SWAP.assoc.traceLeft.SWAP := by
  unfold MState.traceRight MState.SWAP MState.assoc MState.relabel
  simp [ HermitianMat.traceRight, HermitianMat.traceLeft ];
  simp [ Matrix.traceLeft, Matrix.traceRight, HermitianMat.reindex, Matrix.submatrix ];
  simp [ perm_AC_BR ];
  simp [ Fintype.sum_prod_type ]

/-
Tracing out B and R from the purification gives the marginal state on A and C.
-/
private lemma traceRight_relabel_perm_AC_BR_eq_rho_AC :
    ((MState.pure ρ.purify).relabel perm_AC_BR.symm).traceRight = ρ.SWAP.assoc.traceLeft.SWAP := by
  rw [traceRight_relabel_perm_AC_BR]
  rw [MState.purify_spec]

/-
The entropy of the BR marginal of the purification is equal to the entropy of the AC marginal of the original state.
-/
private lemma S_BR_eq_S_AC :
    Sᵥₙ (ρABR ρ).traceLeft = Sᵥₙ ρ.SWAP.assoc.traceLeft.SWAP := by
  rw [traceLeft_ρABR_eq_traceLeft_relabel]
  rw [Sᵥₙ_pure_complement, traceRight_relabel_perm_AC_BR_eq_rho_AC]

private theorem S_AB_purify_eq_S_AB_rho :
    Sᵥₙ ((MState.pure ρ.purify).relabel perm_AB_CR.symm).traceRight = Sᵥₙ ρ.assoc'.traceRight := by
  have h_trace : ((MState.pure ρ.purify).relabel perm_AB_CR.symm).traceRight = ((MState.pure ρ.purify).traceRight).assoc'.traceRight := by
    ext; simp [MState.traceRight, MState.assoc'];
    simp [HermitianMat.traceRight]
    simp [ Matrix.submatrix, Matrix.traceRight ];
    congr! 2;
    ext i j; simp [ perm_AB_CR ] ;
    exact
      Fintype.sum_prod_type fun x =>
        ρ.purify ((i.1, i.2, x.1), x.2) * (starRingEnd ℂ) (ρ.purify ((j.1, j.2, x.1), x.2));
  aesop

/-
The entropy of the AB marginal of the purification is equal to the entropy of the AB marginal of the original state.
-/
private lemma S_AB_eq_S_AB :
    Sᵥₙ (ρABR ρ).assoc'.traceRight = Sᵥₙ ρ.assoc'.traceRight := by
  have h_marginal : Sᵥₙ ((MState.pure ρ.purify).relabel perm_AB_CR.symm).traceRight = Sᵥₙ ρ.assoc'.traceRight := by
    exact S_AB_purify_eq_S_AB_rho ρ
  convert h_marginal using 2;
  convert MState.ext ?_;
  ext i j; simp [ ρABR ] ;
  simp [ MState.traceLeft, MState.relabel, MState.assoc', perm_AB_CR, perm_C_ABR ];
  simp [ MState.SWAP, MState.assoc]
  simp [ MState.pure ];
  simp [ HermitianMat.traceLeft, HermitianMat.traceRight, HermitianMat.reindex ];
  simp [ Matrix.traceLeft, Matrix.traceRight, Matrix.submatrix, Matrix.vecMulVec ];
  simp [ Fintype.sum_prod_type ];
  simp only [Finset.sum_sigma'];
  refine' Finset.sum_bij ( fun x _ => ⟨ x.snd.snd.snd, x.fst, x.snd.fst, x.snd.snd.fst ⟩ ) _ _ _ _ <;> simp
  · aesop;
  · exact fun b => ⟨ b.2.1, b.2.2.1, b.2.2.2, b.1, rfl ⟩

/-- Weak monotonicity of quantum conditional entropy: S(A|B) + S(A|C) ≥ 0. -/
theorem Sᵥₙ_weak_monotonicity :
    let ρAB := ρ.assoc'.traceRight
    let ρAC := ρ.SWAP.assoc.traceLeft.SWAP
    0 ≤ qConditionalEnt ρAB + qConditionalEnt ρAC := by
  -- Apply strong subadditivity to the state ρABR.
  have h_strong_subadditivity := Sᵥₙ_strong_subadditivity (ρABR ρ)
  -- Substitute the equalities for the entropies of the purifications.
  have _ := S_ABR_eq_S_C ρ
  have _ := S_B_eq_S_B ρ
  have _ := S_AB_eq_S_AB ρ
  have _ := S_BR_eq_S_AC ρ
  grind [qConditionalEnt, MState.traceRight_left_assoc', Sᵥₙ_of_SWAP_eq,
    MState.traceLeft_SWAP, MState.traceLeft_right_assoc, MState.traceRight_SWAP]

end weak_monotonicity

/-- Strong subadditivity, stated in terms of conditional entropies.
  Also called the data processing inequality. H(A|BC) ≤ H(A|B). -/
theorem qConditionalEnt_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    qConditionalEnt ρ₁₂₃ ≤ qConditionalEnt ρ₁₂₃.assoc'.traceRight := by
  have := Sᵥₙ_strong_subadditivity ρ₁₂₃
  dsimp at this
  simp only [qConditionalEnt, MState.traceRight_left_assoc']
  linarith

/-- Strong subadditivity, stated in terms of quantum mutual information.
  I(A;BC) ≥ I(A;B). -/
theorem qMutualInfo_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    qMutualInfo ρ₁₂₃ ≥ qMutualInfo ρ₁₂₃.assoc'.traceRight := by
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
    0 ≤ ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  sorry

theorem sandwichedRelRentropy_nonneg (α : ℝ) (ρ σ : MState d) (h : σ.M.ker ≤ ρ.M.ker) :
    0 ≤ if α = 1 then ⟪ρ.M, ρ.M.log - σ.M.log⟫
      else ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace.log / (α - 1) := by
  split_ifs
  · exact inner_log_sub_log_nonneg ρ σ h
  sorry

/-- The Sandwiched Renyi Relative Entropy, defined with ln (nits). Note that at `α = 1` this definition
  switch to the standard Relative Entropy, for continuity. -/
def SandwichedRelRentropy (α : ℝ) (ρ σ : MState d) : ENNReal :=
  open Classical in
  if h : σ.M.ker ≤ ρ.M.ker
  then (.ofNNReal ⟨if α = 1 then
      ⟪ρ.M, ρ.M.log - σ.M.log⟫
    else
      ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace.log / (α - 1),
    sandwichedRelRentropy_nonneg α ρ σ h⟩)
  else ⊤

notation "D̃_" α "(" ρ "‖" σ ")" => SandwichedRelRentropy α ρ σ

/-- The Sandwiched Renyi Relative entropy is additive when the inputs are product states -/
@[simp]
theorem sandwichedRelRentropy_additive (α) (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    D̃_ α(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = D̃_ α(ρ₁‖σ₁) + D̃_ α(ρ₂‖σ₂) := by
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
theorem sandwichedRelRentropy_relabel (ρ σ : MState d) (e : d₂ ≃ d) :
    D̃_ α(ρ.relabel e‖σ.relabel e) = D̃_ α(ρ‖σ) := by
  simp only [SandwichedRelRentropy, MState.relabel_M]
  rw! [HermitianMat.ker_reindex_le_iff] --Why doesn't this `simp`? Because it's an if condition, I'm guessing
  simp [HermitianMat.conj_submatrix]

@[simp]
theorem sandwichedRelRentropy_self (hα : 0 < α) (ρ : MState d) :
  --Technically this holds for all α except for `-1` and `0`. But those are stupid.
  --TODO: Maybe SandwichedRelRentropy should actually be defined differently for α = 0?
    D̃_ α(ρ‖ρ) = 0 := by
  simp? [SandwichedRelRentropy, NNReal.eq_iff] says
    simp only [SandwichedRelRentropy, le_refl, ↓reduceDIte, sub_self, HermitianMat.inner_zero_right,
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

@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem sandwichedRelEntropy_ne_top {ρ σ : MState d} [σ.M.NonSingular] : D̃_ α(ρ‖σ) ≠ ⊤ := by
  simp [SandwichedRelRentropy, HermitianMat.nonSingular_ker_bot]

@[fun_prop]
lemma continuousOn_exponent : ContinuousOn (fun α : ℝ => (1 - α) / (2 * α)) (Set.Ioi 1) := by
  fun_prop (disch := intros; linarith [Set.mem_Ioi.mp ‹_›])

omit [Fintype d₂] [DecidableEq d] [DecidableEq d₂] in
@[fun_prop]
lemma continuous_conj (ρ : HermitianMat d 𝕜) : Continuous (ρ.conj (m := d₂) ·) := by
  simp only [HermitianMat.conj, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  fun_prop

@[fun_prop]
lemma Complex.continuousOn_cpow_const_Ioi (z : ℂ) :
    ContinuousOn (fun r : ℝ => z ^ (r : ℂ)) (Set.Ioi 0) := by
  apply ContinuousOn.const_cpow (f := Complex.ofReal)
  · fun_prop
  · grind [ofReal_ne_zero]

omit [Fintype d] [DecidableEq d] in
lemma HermitianMat.continuousOn_iff_coe {X : Type*} [TopologicalSpace X] {s : Set X}
    (f : X → HermitianMat d 𝕜) :
    ContinuousOn f s ↔ ContinuousOn (fun x => (f x).mat) s := by
  apply Iff.intro;
  · intro hf
    apply ContinuousOn.comp continuous_subtype_val.continuousOn hf
    exact Set.mapsTo_iff_image_subset.mpr fun _ a => a
  · intro h;
    rw [continuousOn_iff_continuous_restrict] at *
    apply Continuous.subtype_mk h

/--
If a parameter-dependent function `f x` is continuous in `x` when evaluated at
the eigenvalues of `A`, then `A.cfc (f x)` is continuous in `x`.
-/
lemma HermitianMat.continuousOn_cfc_param {X : Type*} [TopologicalSpace X] {S : Set X}
    (A : HermitianMat d 𝕜) {f : X → ℝ → ℝ}
    (hf : ∀ i, ContinuousOn (fun x => f x (A.H.eigenvalues i)) S) :
    ContinuousOn (fun x => A.cfc (f x)) S := by
  simp_rw [continuousOn_iff_coe, cfc_toMat_eq_sum_smul_proj A]
  fun_prop

/--
For a fixed Hermitian matrix A, the function x ↦ A^x is continuous for x < 0.
-/
lemma HermitianMat.continuousOn_rpow_neg (A : HermitianMat d ℂ) :
    ContinuousOn (fun x : ℝ => A ^ x) (Set.Iio 0) := by
  apply A.continuousOn_cfc_param
  intro i x hx
  exact (Real.continuousAt_const_rpow' hx.ne).continuousWithinAt

/--
For a fixed Hermitian matrix A, the function x ↦ A^x is continuous for x < 0.
-/
lemma HermitianMat.continuousOn_rpow_pos (A : HermitianMat d 𝕜) :
    ContinuousOn (fun x : ℝ => A ^ x) (Set.Ioi 0) := by
  apply A.continuousOn_cfc_param
  intro i x hx
  exact (Real.continuousAt_const_rpow' hx.ne').continuousWithinAt

/--
The function α ↦ (1 - α) / (2 * α) maps the interval (1, ∞) to (-∞, 0).
-/
lemma maps_to_Iio_of_Ioi_1 : Set.MapsTo (fun α : ℝ => (1 - α) / (2 * α)) (Set.Ioi 1) (Set.Iio 0) := by
  intro x hx
  rw [Set.mem_Ioi] at hx
  rw [Set.mem_Iio]
  have h1 : 1 - x < 0 := by linarith
  have h2 : 0 < 2 * x := by linarith
  exact div_neg_of_neg_of_pos h1 h2

@[fun_prop]
theorem sandwichedRelRentropy.continuousOn (ρ σ : MState d) :
    ContinuousOn (fun α => D̃_ α(ρ‖σ)) (Set.Ioi 0) := by
  --If this turns out too hard, we just need `ContinousAt f 1`.
  --If that's still too hard, we really _just_ need that `(𝓝[≠] 1).tendsto (f 1)`.
  sorry

/-- The Data Processing Inequality for the Sandwiched Renyi relative entropy.
Proved in `https://arxiv.org/pdf/1306.5920`. Seems kind of involved. -/
theorem sandwichedRenyiEntropy_DPI (hα : 1 ≤ α) (ρ σ : MState d) (Φ : CPTPMap d d₂) :
    D̃_ α(Φ ρ‖Φ σ) ≤ D̃_ α(ρ‖σ) := by
  --If we want, we can prove this just for 1 < α, and then use continuity (above) to take the limit as
  -- α → 1.
  sorry

/-- The quantum relative entropy `𝐃(ρ‖σ) := Tr[ρ (log ρ - log σ)]`. -/
def qRelativeEnt (ρ σ : MState d) : ENNReal :=
  D̃_1(ρ‖σ)

notation "𝐃(" ρ "‖" σ ")" => qRelativeEnt ρ σ

/-- Quantum relative entropy as `Tr[ρ (log ρ - log σ)]` when supports are correct. -/
theorem qRelativeEnt_ker {ρ σ : MState d} (h : σ.M.ker ≤ ρ.M.ker) :
    𝐃(ρ‖σ).toEReal = ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  simp [qRelativeEnt, SandwichedRelRentropy, h, EReal.coe_nnreal_eq_coe_real]

open Classical in
theorem qRelativeEnt_eq_neg_Sᵥₙ_add (ρ σ : MState d) :
    (qRelativeEnt ρ σ).toEReal = -(Sᵥₙ ρ : EReal) +
      if σ.M.ker ≤ ρ.M.ker then (-⟪ρ.M, σ.M.log⟫ : EReal) else (⊤ : EReal) := by
  by_cases h : σ.M.ker ≤ ρ.M.ker
  · simp [h, Sᵥₙ_eq_neg_trace_log, qRelativeEnt_ker, inner_sub_right]
    rw [real_inner_comm, sub_eq_add_neg]
  · simp [h]
    exact dif_neg h

/-- The quantum relative entropy is unchanged by `MState.relabel` -/
@[simp]
theorem qRelativeEnt_relabel (ρ σ : MState d) (e : d₂ ≃ d) :
    𝐃(ρ.relabel e‖σ.relabel e) = 𝐃(ρ‖σ) := by
  simp [qRelativeEnt]

/-- "Formula for conversion from operator inequality to quantum relative entropy",
-- Proposition S17 of https://arxiv.org/pdf/2401.01926v2 -/
theorem qRelativeEnt_op_le {ρ σ : MState d} (hpos : 0 < α) (h : ρ.M ≤ α • σ.M) :
    𝐃(ρ‖σ) ≤ ENNReal.ofReal (Real.log α) := by
  sorry

@[simp]
theorem sandwichedRelRentropy_of_unique [Unique d] (ρ σ : MState d) :
    D̃_α(ρ‖σ) = 0 := by
  rcases Subsingleton.allEq ρ default
  rcases Subsingleton.allEq σ default
  simp [SandwichedRelRentropy]

@[simp]
theorem qRelEntropy_of_unique [Unique d] (ρ σ : MState d) :
    𝐃(ρ‖σ) = 0 := by
  exact sandwichedRelRentropy_of_unique ρ σ

theorem sandwichedRelRentropy_heq_congr
      {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂) (hρ : ρ₁ ≍ ρ₂) (hσ : σ₁ ≍ σ₂) :
    D̃_ α(ρ₁‖σ₁) = D̃_ α(ρ₂‖σ₂) := by
  --Why does this thm need to exist? Why not just `subst d₁` and `simp [heq_eq_eq]`? Well, even though d₁
  --and d₂ are equal, we then end up with two distinct instances of `Fintype d₁` and `DecidableEq d₁`,
  --and ρ₁ and ρ₂ refer to them each and so have different types. And then we'd need to `subst` those away
  --too. This is kind of tedious, so it's better to just have this theorem around.
  rw [heq_iff_exists_eq_cast] at hρ hσ
  obtain ⟨_, rfl⟩ := hρ
  obtain ⟨_, rfl⟩ := hσ
  simp [← MState.relabel_cast _ hd]

@[gcongr]
theorem sandwichedRelRentropy_congr {α : ℝ}
      {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂)
        (hρ : ρ₁ = ρ₂.relabel (Equiv.cast hd)) (hσ : σ₁ = σ₂.relabel (Equiv.cast hd)) :
    D̃_ α(ρ₁‖σ₁) = D̃_ α(ρ₂‖σ₂) := by
  subst ρ₁ σ₁
  simp

@[gcongr]
theorem qRelEntropy_heq_congr {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂) (hρ : ρ₁ ≍ ρ₂) (hσ : σ₁ ≍ σ₂) :
    𝐃(ρ₁‖σ₁) = 𝐃(ρ₂‖σ₂) := by
  exact sandwichedRelRentropy_heq_congr hd hρ hσ

/-- Quantum relative entropy when σ has full rank -/
theorem qRelativeEnt_rank {ρ σ : MState d} [σ.M.NonSingular] :
    (𝐃(ρ‖σ) : EReal) = ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  apply qRelativeEnt_ker
  simp [HermitianMat.nonSingular_ker_bot]

/-- The quantum relative entropy is additive when the inputs are product states -/
@[simp]
theorem qRelativeEnt_additive (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    𝐃(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = 𝐃(ρ₁‖σ₁) + 𝐃(ρ₂‖σ₂) := by
  simp [qRelativeEnt]

--BACKPORT
private theorem lowerSemicontinuous_iff {α : Type u_1} {β : Type u_2} [TopologicalSpace α] [Preorder β] {f : α → β} :
    LowerSemicontinuous f ↔ ∀ (x : α), LowerSemicontinuousAt f x := by
  rfl

lemma lowerSemicontinuous_inner (ρ x : MState d) (hx : x.M.ker ≤ ρ.M.ker):
    LowerSemicontinuousAt (fun x ↦ ⟪ρ.M, x.M.log⟫) x := by
  sorry

open Classical in
theorem qRelativeEnt_lowerSemicontinuous_2 (ρ x : MState d) (hx : ¬(x.M.ker ≤ ρ.M.ker)) (y : ENNReal) (hy : y < ⊤) :
    ∀ᶠ (x' : MState d) in nhds x,
      y < (if x'.M.ker ≤ ρ.M.ker then ⟪ρ.M, ρ.M.log - x'.M.log⟫ else ⊤ : EReal) := by
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
theorem qRelEntropy_self (ρ : MState d) : 𝐃(ρ‖ρ) = 0 := by
  simp [qRelativeEnt]

@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem qRelativeEnt_ne_top {ρ σ : MState d} [σ.M.NonSingular] : 𝐃(ρ‖σ) ≠ ⊤ := by
  rw [qRelativeEnt]
  finiteness

/-- `I(A:B) = 𝐃(ρᴬᴮ‖ρᴬ ⊗ ρᴮ)` -/
theorem qMutualInfo_as_qRelativeEnt (ρ : MState (dA × dB)) :
    qMutualInfo ρ = (𝐃(ρ‖ρ.traceRight ⊗ᴹ ρ.traceLeft) : EReal) := by
  sorry

theorem qRelEntropy_le_add_of_le_smul (ρ : MState d) {σ₁ σ₂ : MState d} (hσ : σ₁.M ≤ α • σ₂.M) :
    𝐃(ρ‖σ₁) ≤ 𝐃(ρ‖σ₂) + ENNReal.ofReal (Real.log α)
    := by
  sorry

end relative_entropy
