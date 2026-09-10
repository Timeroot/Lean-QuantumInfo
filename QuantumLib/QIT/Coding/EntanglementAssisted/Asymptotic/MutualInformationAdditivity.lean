/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Coding.EntanglementAssisted.Asymptotic.ProtocolLifting
public import QuantumLib.QIT.HypothesisTesting.DPI
import QuantumLib.QIT.States.Purification.Uhlmann

/-!
# Ordinary mutual-information additivity

This module is part of the entanglement-assisted classical communication
asymptotic proof spine.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Topology Kronecker
open Filter

universe u v w x y

noncomputable section

namespace CPTPOp

open QIT

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

variable (N : CPTPMap a b)

set_option maxRecDepth 4000 in
/-- Any pure input-reference objective whose reference system contains an
input-copy reference is bounded by the optimized channel mutual information.

This is the ordinary mutual-information analogue of the hypothesis-testing
arbitrary-reference bridge, and formalizes the source step
`sup_{ρ_RA} I(R;B) = I(N)` when the reference is large enough
from Khatri--Wilde, `Chapters/EA_capacity.tex`, lines 1039-1043. -/
theorem entanglementAssistedMutualInformation_le_information_of_card_le
    [Nonempty a] {r : Type w} [Fintype r] [DecidableEq r]
    (ψ : Ket (r × a)) (hcard : Fintype.card a ≤ Fintype.card r) :
    N.entanglementAssistedMutualInformation ψ ≤
      N.entanglementAssistedInformation := by
  let φ : Ket (a × a) := ψ.state.traceLeft.canonicalPurification
  have hφ : φ.Purifies ψ.state.traceLeft :=
    ψ.state.traceLeft.canonicalPurification_purifies
  have hψ : ψ.Purifies ψ.state.traceLeft :=
    ψ.purifies_traceLeft
  rcases Ket.exists_referenceIsometry_applyKet_eq_of_purifies_same_state
      hφ hψ hcard with ⟨V, hV⟩
  have hout :
      N.entanglementAssistedOutputState ψ =
        ((CPTPOp.ofReferenceIsometry V).prod (CPTPOp.id (dIn := b)))
          (N.entanglementAssistedOutputState φ) := by
    rw [hV]
    simpa [CPTPOp.entanglementAssistedOutputState, CPTPOp.hypothesisTestingOutputState]
      using N.hypothesisTestingOutputState_applyReferenceIsometry V φ
  unfold CPTPOp.entanglementAssistedMutualInformation
  rw [hout]
  have hdpi :=
    QIT.mutualInformation_dataProcessing_local_channels_ge
      (N.entanglementAssistedOutputState φ)
      (CPTPOp.ofReferenceIsometry V) (CPTPOp.id (dIn := b))
  exact hdpi.trans (N.entanglementAssistedMutualInformation_le_information φ)

private theorem card_le_purified_reference
    {a₀ : Type u} {r : Type w} [Fintype a₀] [Fintype r] [Nonempty r] :
    Fintype.card a₀ ≤ Fintype.card ((r × a₀) × r) := by
  have hrpos : 0 < Fintype.card r := Fintype.card_pos_iff.mpr inferInstance
  have h1 : Fintype.card a₀ ≤ Fintype.card a₀ * Fintype.card r :=
    Nat.le_mul_of_pos_right (Fintype.card a₀) hrpos
  have h2 : Fintype.card a₀ * Fintype.card r ≤
      (Fintype.card a₀ * Fintype.card r) * Fintype.card r :=
    Nat.le_mul_of_pos_right (Fintype.card a₀ * Fintype.card r) hrpos
  calc
    Fintype.card a₀ ≤ Fintype.card a₀ * Fintype.card r := h1
    _ ≤ (Fintype.card a₀ * Fintype.card r) * Fintype.card r := h2
    _ = Fintype.card ((r × a₀) × r) := by
      simp [Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm]

set_option maxRecDepth 4000 in
/-- Mixed input-reference output states are bounded by the optimized channel
mutual information.

The proof purifies the mixed input-reference state, traces out the extra
purifying reference after the channel use, and applies reference-side
data processing together with the arbitrary-reference pure-input bridge.
This follows Khatri--Wilde, `Chapters/EA_capacity.tex`, lines 1039-1043. -/
theorem mixedInputOutput_mutualInformation_le_information
    [Nonempty a] {r : Type w} [Fintype r] [DecidableEq r]
    (ρ : MState (r × a)) :
    mutualInformation (((CPTPOp.id (dIn := r)).prod N) ρ) ≤
      N.entanglementAssistedInformation := by
  have : Nonempty r := by
    rcases ρ.nonempty with ⟨ra⟩
    exact ⟨ra.1⟩
  let ψ : Ket (((r × a) × r) × a) :=
    ρ.purifiedInputForHypothesisTestingDPI
  let D : CPTPMap ((r × a) × r) r :=
    CPTPOp.traceOutLeft (r × a) r
  have hstate :
      (D.prod (CPTPOp.id (dIn := b))) (N.entanglementAssistedOutputState ψ) =
        ((CPTPOp.id (dIn := r)).prod N) ρ := by
    calc
      (D.prod (CPTPOp.id (dIn := b))) (N.entanglementAssistedOutputState ψ) =
        (D.prod (CPTPOp.id (dIn := b)))
          (((CPTPOp.id (dIn := (r × a) × r)).prod N) ψ.state) := rfl
      _ = ((CPTPOp.id (dIn := r)).prod N)
          (((D.prod (CPTPOp.id (dIn := a))) ψ.state)) := by
          exact CPTPOp.traceOutLeft_prod_id_applyState_id_prod
            (p := r × a) (r := r) N ψ.state
      _ = ((CPTPOp.id (dIn := r)).prod N) ρ := by
          rw [MState.traceOut_purifiedInputForHypothesisTestingDPI]
  rw [← hstate]
  have hdpi :=
    QIT.mutualInformation_dataProcessing_local_channels_ge
      (N.entanglementAssistedOutputState ψ) D (CPTPOp.id (dIn := b))
  have hcard :
      Fintype.card a ≤ Fintype.card ((r × a) × r) :=
    card_le_purified_reference (a₀ := a) (r := r)
  exact hdpi.trans (N.entanglementAssistedMutualInformation_le_information_of_card_le ψ hcard)

/-- Product pure input for the entanglement-assisted objective of a product
channel, repartitioned from `(A₁ × A₁) × (A₂ × A₂)` to
`(A₁ × A₂) × (A₁ × A₂)`. -/
def entanglementAssistedProductInput
    {a₁ : Type u} {a₂ : Type w}
    [Fintype a₁] [DecidableEq a₁] [Fintype a₂] [DecidableEq a₂]
    (ψ : Ket (a₁ × a₁)) (φ : Ket (a₂ × a₂)) :
    Ket ((a₁ × a₂) × (a₁ × a₂)) :=
  (ψ.prod φ).reindex
    (Equiv.prodProdProdComm a₁ a₁ a₂ a₂)

set_option maxRecDepth 4000 in
/-- Product-channel entanglement-assisted output states factor on product
inputs. This is the state-level additivity step in
Khatri--Wilde, `Chapters/EA_capacity.tex`, lines 1044-1058. -/
theorem entanglementAssistedOutputState_prod
    {a₁ : Type u} {b₁ : Type v} {a₂ : Type w} {b₂ : Type x}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (N₁ : CPTPMap a₁ b₁) (N₂ : CPTPMap a₂ b₂)
    (ψ : Ket (a₁ × a₁)) (φ : Ket (a₂ × a₂)) :
    (N₁.prod N₂).entanglementAssistedOutputState
        (entanglementAssistedProductInput ψ φ) =
      (N₁.entanglementAssistedOutputState ψ).bipartiteProduct
        (N₂.entanglementAssistedOutputState φ) := by
  unfold CPTPOp.entanglementAssistedOutputState entanglementAssistedProductInput
  rw [Ket.reindex_state, Ket.prod_state]
  exact CPTPOp.applyState_prod_reindex_prodProdProdComm
    N₁ N₂ ψ.state φ.state

/-- Product-channel mutual information is superadditive. -/
theorem entanglementAssistedInformation_prod_lower_bound
    {a₁ : Type u} {b₁ : Type v} {a₂ : Type w} {b₂ : Type x}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Nonempty a₁] [Nonempty a₂]
    (N₁ : CPTPMap a₁ b₁) (N₂ : CPTPMap a₂ b₂) :
    N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation ≤
      (N₁.prod N₂).entanglementAssistedInformation := by
  obtain ⟨ψ, hψ⟩ := N₁.exists_entanglementAssistedInformation_maximizer
  obtain ⟨φ, hφ⟩ := N₂.exists_entanglementAssistedInformation_maximizer
  have hcandidate :
      (N₁.prod N₂).entanglementAssistedMutualInformation
          (entanglementAssistedProductInput ψ φ) =
        N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation := by
    unfold CPTPOp.entanglementAssistedMutualInformation
    rw [CPTPOp.entanglementAssistedOutputState_prod]
    rw [MState.mutualInformation_bipartiteProduct]
    change N₁.entanglementAssistedMutualInformation ψ +
        N₂.entanglementAssistedMutualInformation φ =
      N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation
    rw [← hψ, ← hφ]
  calc
    N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation =
        (N₁.prod N₂).entanglementAssistedMutualInformation
          (entanglementAssistedProductInput ψ φ) := hcandidate.symm
    _ ≤ (N₁.prod N₂).entanglementAssistedInformation :=
        (N₁.prod N₂).entanglementAssistedMutualInformation_le_information
          (entanglementAssistedProductInput ψ φ)

set_option maxRecDepth 4000 in
/-- Pointwise upper bound for the product-channel entanglement-assisted
objective:
`I(R;B₁B₂)_{(N₁⊗N₂)(ψ)} ≤ I(N₁)+I(N₂)`.

This formalizes the chain-rule argument
`I(R;B₁B₂) = I(R;B₁)+I(RB₁;B₂)-I(B₁;B₂)` together with nonnegativity and
the mixed-input optimization bridge from Khatri--Wilde,
`Chapters/EA_capacity.tex`, lines 1078-1100. -/
theorem entanglementAssistedMutualInformation_prod_le_information_add
    {a₁ : Type u} {b₁ : Type v} {a₂ : Type w} {b₂ : Type x}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Nonempty a₁] [Nonempty a₂]
    (N₁ : CPTPMap a₁ b₁) (N₂ : CPTPMap a₂ b₂)
    (ψ : Ket ((a₁ × a₂) × (a₁ × a₂))) :
    (N₁.prod N₂).entanglementAssistedMutualInformation ψ ≤
      N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation := by
  let R := (a₁ × a₂)
  let ρout : MState (R × (b₁ × b₂)) :=
    (N₁.prod N₂).entanglementAssistedOutputState ψ
  let ρleft : MState ((R × b₁) × b₂) :=
    ρout.reindex (Equiv.prodAssoc R b₁ b₂).symm
  let τ₂ : MState ((R × b₁) × a₂) :=
    MState.reindex ((((CPTPOp.id (dIn := R)).prod (N₁.prod (CPTPOp.id (dIn := a₂)))) ψ.state))
      (Equiv.prodAssoc R b₁ a₂).symm
  let τ₁ : MState (R × a₁) :=
    (ψ.state.reindex (Equiv.prodAssoc R a₁ a₂).symm).marginalAB
  have hρleft :
      ρleft = (((CPTPOp.id (dIn := R × b₁)).prod N₂) τ₂) := by
    unfold ρleft ρout τ₂ R
    rw [CPTPOp.entanglementAssistedOutputState]
    exact MState.applyState_id_prod_prod_assoc_symm N₁ N₂ ψ.state
  have hterm₁ :
      mutualInformation ρleft.marginalAB ≤ N₁.entanglementAssistedInformation := by
    rw [hρleft]
    rw [MState.marginalAB_eq_traceRight]
    rw [MState.traceRight_applyState_id_prod]
    change mutualInformation τ₂.marginalAB ≤ N₁.entanglementAssistedInformation
    rw [MState.partialProductOutput_marginalAB]
    exact N₁.mixedInputOutput_mutualInformation_le_information τ₁
  have hterm₂ :
      mutualInformation ρleft ≤ N₂.entanglementAssistedInformation := by
    rw [hρleft]
    exact N₂.mixedInputOutput_mutualInformation_le_information τ₂
  unfold CPTPOp.entanglementAssistedMutualInformation
  change mutualInformation ρout ≤
    N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation
  calc
    mutualInformation ρout =
        mutualInformation (ρleft.reindex (Equiv.prodAssoc R b₁ b₂)) := by
          change mutualInformation ρout =
            mutualInformation ((ρout.reindex (Equiv.prodAssoc R b₁ b₂).symm).reindex
              (Equiv.prodAssoc R b₁ b₂))
          rw [MState.reindex_symm_reindex]
    _ ≤ mutualInformation ρleft.marginalAB + mutualInformation ρleft :=
        MState.mutualInformation_assoc_le ρleft
    _ ≤ N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation :=
        add_le_add hterm₁ hterm₂

/-- Product-channel mutual information is subadditive. -/
theorem entanglementAssistedInformation_prod_upper_bound
    {a₁ : Type u} {b₁ : Type v} {a₂ : Type w} {b₂ : Type x}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Nonempty a₁] [Nonempty a₂]
    (N₁ : CPTPMap a₁ b₁) (N₂ : CPTPMap a₂ b₂) :
    (N₁.prod N₂).entanglementAssistedInformation ≤
      N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation := by
  obtain ⟨ψ, hψ⟩ := (N₁.prod N₂).exists_entanglementAssistedInformation_maximizer
  calc
    (N₁.prod N₂).entanglementAssistedInformation =
        (N₁.prod N₂).entanglementAssistedMutualInformation ψ := hψ
    _ ≤ N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation :=
        entanglementAssistedMutualInformation_prod_le_information_add N₁ N₂ ψ

/-- Entanglement-assisted channel mutual information is additive under product
channels:
`I(N₁ ⊗ N₂) = I(N₁) + I(N₂)`.

This is the formal statement corresponding to Khatri--Wilde,
`Chapters/EA_capacity.tex`, lines 1023-1115. -/
theorem entanglementAssistedInformation_prod
    {a₁ : Type u} {b₁ : Type v} {a₂ : Type w} {b₂ : Type x}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Nonempty a₁] [Nonempty a₂]
    (N₁ : CPTPMap a₁ b₁) (N₂ : CPTPMap a₂ b₂) :
    (N₁.prod N₂).entanglementAssistedInformation =
      N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation := by
  exact le_antisymm
    (entanglementAssistedInformation_prod_upper_bound N₁ N₂)
    (entanglementAssistedInformation_prod_lower_bound N₁ N₂)

private theorem entanglementAssistedInformation_unit :
    (CPTPOp.unit : CPTPMap PUnit.{u + 1} PUnit.{v + 1}).entanglementAssistedInformation = 0 := by
  obtain ⟨ψ, hψ⟩ :=
    (CPTPOp.unit : CPTPMap PUnit.{u + 1} PUnit.{v + 1}).exists_entanglementAssistedInformation_maximizer
  rw [hψ]
  unfold CPTPOp.entanglementAssistedMutualInformation
  exact MState.mutualInformation_punit_punit_eq_zero _

/-- Tensor-power corollary of product-channel additivity:
`I(N^{⊗n}) = n I(N)`.

This is the additivity simplification used in
Khatri--Wilde, `Chapters/EA_capacity.tex`, lines 1118-1124. -/
theorem entanglementAssistedInformation_tensorPower_eq_mul
    [Nonempty a] (n : ℕ) :
    (N.tensorPower n).entanglementAssistedInformation =
      (n : ℝ) * N.entanglementAssistedInformation := by
  induction n with
  | zero =>
      rw [CPTPOp.tensorPower_zero]
      calc
        (CPTPOp.unit : CPTPMap (QIT.TensorPower a 0) (QIT.TensorPower b 0)).entanglementAssistedInformation =
            0 := by
            exact entanglementAssistedInformation_unit
        _ = ((0 : ℕ) : ℝ) * N.entanglementAssistedInformation := by norm_num
  | succ n ih =>
      have : Nonempty (QIT.TensorPower a n) :=
        tensorPower_nonempty_of_nonempty (α := a) n
      rw [CPTPOp.tensorPower_succ]
      calc
        (N.prod (N.tensorPower n)).entanglementAssistedInformation =
            N.entanglementAssistedInformation +
              (N.tensorPower n).entanglementAssistedInformation :=
            CPTPOp.entanglementAssistedInformation_prod N (N.tensorPower n)
        _ = ((n + 1 : ℕ) : ℝ) * N.entanglementAssistedInformation := by
            rw [ih]
            rw [Nat.cast_add, Nat.cast_one]
            ring

end CPTPOp

end
