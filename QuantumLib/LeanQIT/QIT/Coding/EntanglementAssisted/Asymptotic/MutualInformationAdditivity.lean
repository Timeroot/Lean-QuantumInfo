/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Asymptotic.ProtocolLifting
public import QIT.HypothesisTesting.DPI
import QIT.States.Purification.Uhlmann

/-!
# Ordinary mutual-information additivity

This module is part of the entanglement-assisted classical communication
asymptotic proof spine.  It was split out mechanically from the historical
`EntanglementAssistedAsymptotic` files; theorem statements and proof routes are
unchanged.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Topology
open Filter

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace Channel

variable (N : Channel a b)

/-- Any pure input-reference objective whose reference system contains an
input-copy reference is bounded by the optimized channel mutual information.

This is the ordinary mutual-information analogue of the hypothesis-testing
arbitrary-reference bridge, and formalizes the source step
`sup_{ρ_RA} I(R;B) = I(N)` when the reference is large enough
from Khatri--Wilde, `Chapters/EA_capacity.tex`, lines 1039-1043. -/
theorem entanglementAssistedMutualInformation_le_information_of_card_le
    [Nonempty a] {r : Type w} [Fintype r] [DecidableEq r]
    (ψ : PureVector (Prod r a)) (hcard : Fintype.card a ≤ Fintype.card r) :
    N.entanglementAssistedMutualInformation ψ ≤
      N.entanglementAssistedInformation := by
  let φ : PureVector (Prod a a) := ψ.state.marginalB.canonicalPurification
  have hφ : φ.Purifies ψ.state.marginalB :=
    ψ.state.marginalB.canonicalPurification_purifies
  have hψ : ψ.Purifies ψ.state.marginalB :=
    ψ.purifies_marginalB
  rcases PureVector.exists_referenceIsometry_applyPureVector_eq_of_purifies_same_state
      hφ hψ hcard with ⟨V, hV⟩
  have hout :
      N.entanglementAssistedOutputState ψ =
        ((Channel.ofReferenceIsometry V).prod (Channel.idChannel b)).applyState
          (N.entanglementAssistedOutputState φ) := by
    rw [hV]
    simpa [Channel.entanglementAssistedOutputState, Channel.hypothesisTestingOutputState]
      using N.hypothesisTestingOutputState_applyReferenceIsometry V φ
  unfold Channel.entanglementAssistedMutualInformation
  rw [hout]
  have hdpi :=
    QIT.mutualInformation_dataProcessing_local_channels_ge
      (N.entanglementAssistedOutputState φ)
      (Channel.ofReferenceIsometry V) (Channel.idChannel b)
  exact hdpi.trans (N.entanglementAssistedMutualInformation_le_information φ)

private theorem card_le_purified_reference
    {a₀ : Type u} {r : Type w} [Fintype a₀] [Fintype r] [Nonempty r] :
    Fintype.card a₀ ≤ Fintype.card (Prod (Prod r a₀) r) := by
  have hrpos : 0 < Fintype.card r := Fintype.card_pos_iff.mpr inferInstance
  have h1 : Fintype.card a₀ ≤ Fintype.card a₀ * Fintype.card r :=
    Nat.le_mul_of_pos_right (Fintype.card a₀) hrpos
  have h2 : Fintype.card a₀ * Fintype.card r ≤
      (Fintype.card a₀ * Fintype.card r) * Fintype.card r :=
    Nat.le_mul_of_pos_right (Fintype.card a₀ * Fintype.card r) hrpos
  calc
    Fintype.card a₀ ≤ Fintype.card a₀ * Fintype.card r := h1
    _ ≤ (Fintype.card a₀ * Fintype.card r) * Fintype.card r := h2
    _ = Fintype.card (Prod (Prod r a₀) r) := by
      simp [Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm]

/-- Mixed input-reference output states are bounded by the optimized channel
mutual information.

The proof purifies the mixed input-reference state, traces out the extra
purifying reference after the channel use, and applies reference-side
data processing together with the arbitrary-reference pure-input bridge.
This follows Khatri--Wilde, `Chapters/EA_capacity.tex`, lines 1039-1043. -/
theorem mixedInputOutput_mutualInformation_le_information
    [Nonempty a] {r : Type w} [Fintype r] [DecidableEq r]
    (ρ : State (Prod r a)) :
    mutualInformation (((Channel.idChannel r).prod N).applyState ρ) ≤
      N.entanglementAssistedInformation := by
  haveI : Nonempty r := by
    rcases ρ.nonempty with ⟨ra⟩
    exact ⟨ra.1⟩
  let ψ : PureVector (Prod (Prod (Prod r a) r) a) :=
    ρ.purifiedInputForHypothesisTestingDPI
  let D : Channel (Prod (Prod r a) r) r :=
    Channel.traceOutLeft (Prod r a) r
  have hstate :
      (D.prod (Channel.idChannel b)).applyState (N.entanglementAssistedOutputState ψ) =
        ((Channel.idChannel r).prod N).applyState ρ := by
    calc
      (D.prod (Channel.idChannel b)).applyState (N.entanglementAssistedOutputState ψ) =
        (D.prod (Channel.idChannel b)).applyState
          (((Channel.idChannel (Prod (Prod r a) r)).prod N).applyState ψ.state) := rfl
      _ = ((Channel.idChannel r).prod N).applyState
          (((D.prod (Channel.idChannel a)).applyState ψ.state)) := by
          exact Channel.traceOutLeft_prod_id_applyState_id_prod
            (p := Prod r a) (r := r) N ψ.state
      _ = ((Channel.idChannel r).prod N).applyState ρ := by
          rw [State.traceOut_purifiedInputForHypothesisTestingDPI]
  rw [← hstate]
  have hdpi :=
    QIT.mutualInformation_dataProcessing_local_channels_ge
      (N.entanglementAssistedOutputState ψ) D (Channel.idChannel b)
  have hcard :
      Fintype.card a ≤ Fintype.card (Prod (Prod r a) r) :=
    card_le_purified_reference (a₀ := a) (r := r)
  exact hdpi.trans (N.entanglementAssistedMutualInformation_le_information_of_card_le ψ hcard)

/-- Product pure input for the entanglement-assisted objective of a product
channel, repartitioned from `(A₁ × A₁) × (A₂ × A₂)` to
`(A₁ × A₂) × (A₁ × A₂)`. -/
def entanglementAssistedProductInput
    {a₁ : Type u} {a₂ : Type w}
    [Fintype a₁] [DecidableEq a₁] [Fintype a₂] [DecidableEq a₂]
    (ψ : PureVector (Prod a₁ a₁)) (φ : PureVector (Prod a₂ a₂)) :
    PureVector (Prod (Prod a₁ a₂) (Prod a₁ a₂)) :=
  (ψ.prod φ).reindex
    (State.bipartiteProductEquiv (a1 := a₁) (b1 := a₁) (a2 := a₂) (b2 := a₂))

/-- Applying a product channel to a repartitioned product input yields the
repartitioned product of the two individual output states. -/
private theorem applyState_prod_reindex_entanglementAssistedProductInput
    {a₁ : Type u} {b₁ : Type v} {a₂ : Type w} {b₂ : Type x}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (N₁ : Channel a₁ b₁) (N₂ : Channel a₂ b₂)
    (ρ : State (Prod a₁ a₁)) (σ : State (Prod a₂ a₂)) :
    (((Channel.idChannel (Prod a₁ a₂)).prod (N₁.prod N₂)).applyState
        ((ρ.prod σ).reindex
          (State.bipartiteProductEquiv
            (a1 := a₁) (b1 := a₁) (a2 := a₂) (b2 := a₂)))) =
      ((((Channel.idChannel a₁).prod N₁).applyState ρ).prod
          (((Channel.idChannel a₂).prod N₂).applyState σ)).reindex
        (State.bipartiteProductEquiv
          (a1 := a₁) (b1 := b₁) (a2 := a₂) (b2 := b₂)) := by
  apply State.ext
  ext x y
  rcases x with ⟨xR, xB⟩
  rcases y with ⟨yR, yB⟩
  rcases xR with ⟨xR1, xR2⟩
  rcases xB with ⟨xB1, xB2⟩
  rcases yR with ⟨yR1, yR2⟩
  rcases yB with ⟨yB1, yB2⟩
  simp only [Channel.applyState, Channel.prod, State.reindex_matrix,
    State.prod_matrix_kronecker, Matrix.submatrix_apply]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  have hslice :
      (fun j j' =>
          (Matrix.kronecker ρ.matrix σ.matrix).submatrix
            (State.bipartiteProductEquiv
              (a1 := a₁) (b1 := a₁) (a2 := a₂) (b2 := a₂)).symm
            (State.bipartiteProductEquiv
              (a1 := a₁) (b1 := a₁) (a2 := a₂) (b2 := a₂)).symm
            (((xR1, xR2), (xB1, xB2)).1, j)
            (((yR1, yR2), (yB1, yB2)).1, j')) =
        Matrix.kronecker
          (fun i i' => ρ.matrix (xR1, i) (yR1, i'))
          (fun k k' => σ.matrix (xR2, k) (yR2, k')) := by
    ext z z'
    rcases z with ⟨z1, z2⟩
    rcases z' with ⟨z1', z2'⟩
    simp [State.bipartiteProductEquiv, Matrix.kronecker,
      Matrix.kroneckerMap_apply]
  rw [hslice]
  change MatrixMap.kron N₁.map N₂.map
      (Matrix.kronecker
        (fun i i' => ρ.matrix (xR1, i) (yR1, i'))
        (fun k k' => σ.matrix (xR2, k) (yR2, k')))
      (xB1, xB2) (yB1, yB2) = _
  rw [MatrixMap.kron_apply_kronecker]
  simp [State.bipartiteProductEquiv, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  rw [MatrixMap.kron_idChannel_left_apply_slice]

/-- Product-channel entanglement-assisted output states factor on product
inputs. This is the state-level additivity step in
Khatri--Wilde, `Chapters/EA_capacity.tex`, lines 1044-1058. -/
theorem entanglementAssistedOutputState_prod
    {a₁ : Type u} {b₁ : Type v} {a₂ : Type w} {b₂ : Type x}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (N₁ : Channel a₁ b₁) (N₂ : Channel a₂ b₂)
    (ψ : PureVector (Prod a₁ a₁)) (φ : PureVector (Prod a₂ a₂)) :
    (N₁.prod N₂).entanglementAssistedOutputState
        (entanglementAssistedProductInput ψ φ) =
      (N₁.entanglementAssistedOutputState ψ).bipartiteProduct
        (N₂.entanglementAssistedOutputState φ) := by
  unfold Channel.entanglementAssistedOutputState entanglementAssistedProductInput
  rw [PureVector.reindex_state, PureVector.prod_state]
  exact applyState_prod_reindex_entanglementAssistedProductInput
    N₁ N₂ ψ.state φ.state

/-- Product-channel mutual information is superadditive. -/
theorem entanglementAssistedInformation_prod_lower_bound
    {a₁ : Type u} {b₁ : Type v} {a₂ : Type w} {b₂ : Type x}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Nonempty a₁] [Nonempty a₂]
    (N₁ : Channel a₁ b₁) (N₂ : Channel a₂ b₂) :
    N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation ≤
      (N₁.prod N₂).entanglementAssistedInformation := by
  obtain ⟨ψ, hψ⟩ := N₁.exists_entanglementAssistedInformation_maximizer
  obtain ⟨φ, hφ⟩ := N₂.exists_entanglementAssistedInformation_maximizer
  have hcandidate :
      (N₁.prod N₂).entanglementAssistedMutualInformation
          (entanglementAssistedProductInput ψ φ) =
        N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation := by
    unfold Channel.entanglementAssistedMutualInformation
    rw [Channel.entanglementAssistedOutputState_prod]
    rw [State.mutualInformation_bipartiteProduct]
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
    (N₁ : Channel a₁ b₁) (N₂ : Channel a₂ b₂)
    (ψ : PureVector (Prod (Prod a₁ a₂) (Prod a₁ a₂))) :
    (N₁.prod N₂).entanglementAssistedMutualInformation ψ ≤
      N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation := by
  let R := Prod a₁ a₂
  let ρout : State (Prod R (Prod b₁ b₂)) :=
    (N₁.prod N₂).entanglementAssistedOutputState ψ
  let ρleft : State (Prod (Prod R b₁) b₂) :=
    ρout.reindex (Equiv.prodAssoc R b₁ b₂).symm
  let τ₂ : State (Prod (Prod R b₁) a₂) :=
    ((((Channel.idChannel R).prod (N₁.prod (Channel.idChannel a₂))).applyState ψ.state).reindex
      (Equiv.prodAssoc R b₁ a₂).symm)
  let τ₁ : State (Prod R a₁) :=
    (ψ.state.reindex (Equiv.prodAssoc R a₁ a₂).symm).marginalAB
  have hρleft :
      ρleft = (((Channel.idChannel (Prod R b₁)).prod N₂).applyState τ₂) := by
    unfold ρleft ρout τ₂ R
    rw [Channel.entanglementAssistedOutputState]
    exact State.applyState_id_prod_prod_assoc_symm N₁ N₂ ψ.state
  have hterm₁ :
      mutualInformation ρleft.marginalAB ≤ N₁.entanglementAssistedInformation := by
    rw [hρleft]
    rw [State.marginalAB_eq_marginalA]
    rw [State.marginalA_applyState_id_prod]
    change mutualInformation τ₂.marginalAB ≤ N₁.entanglementAssistedInformation
    rw [State.partialProductOutput_marginalAB]
    exact N₁.mixedInputOutput_mutualInformation_le_information τ₁
  have hterm₂ :
      mutualInformation ρleft ≤ N₂.entanglementAssistedInformation := by
    rw [hρleft]
    exact N₂.mixedInputOutput_mutualInformation_le_information τ₂
  unfold Channel.entanglementAssistedMutualInformation
  change mutualInformation ρout ≤
    N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation
  calc
    mutualInformation ρout =
        mutualInformation (ρleft.reindex (Equiv.prodAssoc R b₁ b₂)) := by
          change mutualInformation ρout =
            mutualInformation ((ρout.reindex (Equiv.prodAssoc R b₁ b₂).symm).reindex
              (Equiv.prodAssoc R b₁ b₂))
          rw [state_reindex_symm_reindex]
    _ ≤ mutualInformation ρleft.marginalAB + mutualInformation ρleft :=
        State.mutualInformation_assoc_le ρleft
    _ ≤ N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation :=
        add_le_add hterm₁ hterm₂

/-- Product-channel mutual information is subadditive. -/
theorem entanglementAssistedInformation_prod_upper_bound
    {a₁ : Type u} {b₁ : Type v} {a₂ : Type w} {b₂ : Type x}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Nonempty a₁] [Nonempty a₂]
    (N₁ : Channel a₁ b₁) (N₂ : Channel a₂ b₂) :
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
    (N₁ : Channel a₁ b₁) (N₂ : Channel a₂ b₂) :
    (N₁.prod N₂).entanglementAssistedInformation =
      N₁.entanglementAssistedInformation + N₂.entanglementAssistedInformation := by
  exact le_antisymm
    (entanglementAssistedInformation_prod_upper_bound N₁ N₂)
    (entanglementAssistedInformation_prod_lower_bound N₁ N₂)

private theorem entanglementAssistedInformation_unit :
    (Channel.unit : Channel PUnit.{u + 1} PUnit.{v + 1}).entanglementAssistedInformation = 0 := by
  obtain ⟨ψ, hψ⟩ :=
    (Channel.unit : Channel PUnit.{u + 1} PUnit.{v + 1}).exists_entanglementAssistedInformation_maximizer
  rw [hψ]
  unfold Channel.entanglementAssistedMutualInformation
  exact State.mutualInformation_punit_punit_eq_zero _

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
      rw [Channel.tensorPower_zero]
      calc
        (Channel.unit : Channel (QIT.TensorPower a 0) (QIT.TensorPower b 0)).entanglementAssistedInformation =
            0 := by
            exact entanglementAssistedInformation_unit
        _ = ((0 : ℕ) : ℝ) * N.entanglementAssistedInformation := by norm_num
  | succ n ih =>
      haveI : Nonempty (QIT.TensorPower a n) :=
        tensorPower_nonempty_of_nonempty (α := a) n
      rw [Channel.tensorPower_succ]
      calc
        (N.prod (N.tensorPower n)).entanglementAssistedInformation =
            N.entanglementAssistedInformation +
              (N.tensorPower n).entanglementAssistedInformation :=
            Channel.entanglementAssistedInformation_prod N (N.tensorPower n)
        _ = ((n + 1 : ℕ) : ℝ) * N.entanglementAssistedInformation := by
            rw [ih]
            rw [Nat.cast_add, Nat.cast_one]
            ring

end Channel

end

end QIT
