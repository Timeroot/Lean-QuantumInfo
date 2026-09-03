/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.OneShot.Lower.Petz
public import QIT.Coding.EntanglementAssisted.OneShot.WeakConverse
public import QIT.Coding.EntanglementAssisted.Renyi.Petz.Additivity
public import QIT.Coding.EntanglementAssisted.Renyi.Petz.Limit
public import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Additivity.ChannelProduct
public import QIT.HypothesisTesting.PetzComparison
public import QIT.Information.Entropy.EntropyTensorPower
public import QIT.Information.AlickiFannesWinter
import QIT.Util.TensorPower

/-!
# Asymptotic basic helpers

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

private theorem log2_pow_nat (x : ℝ) (n : ℕ) :
    log2 (x ^ n) = (n : ℝ) * log2 x := by
  unfold log2
  rw [Real.log_pow]
  ring

namespace PetzRenyiAlpha

/-- The left-to-one filter on the source range `0 < alpha < 1` is nontrivial:
every one-sided neighborhood of `1` contains an admissible Renyi parameter. -/
theorem leftToOne_neBot : Filter.NeBot PetzRenyiAlpha.leftToOne := by
  unfold PetzRenyiAlpha.leftToOne
  refine Filter.comap_neBot ?_
  intro t ht
  have hflt :
      (t ∩ Set.Iio (1 : ℝ)) ∩ Set.Ioi (0 : ℝ) ∈
        nhdsWithin (1 : ℝ) (Set.Iio 1) := by
    exact Filter.inter_mem
      (Filter.inter_mem ht self_mem_nhdsWithin)
      (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds zero_lt_one))
  haveI : Filter.NeBot (nhdsWithin (1 : ℝ) (Set.Iio 1)) :=
    nhdsWithin_Iio_neBot (α := ℝ) (a := 1) (b := 1) le_rfl
  rcases Filter.nonempty_of_mem hflt with ⟨x, hx⟩
  refine ⟨⟨x, ?_⟩, ?_⟩
  · exact ⟨hx.2, hx.1.2⟩
  · exact hx.1.1

end PetzRenyiAlpha

namespace MatrixMap

variable {α : Type u} {β : Type v} {γ : Type w}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Fintype γ] [DecidableEq γ]

/-- Relabel the output basis of a finite matrix map. -/
def outputReindex (Phi : MatrixMap α β) (e : β ≃ γ) : MatrixMap α γ where
  toFun X := Matrix.reindex e e (Phi X)
  map_add' X Y := by
    ext i j
    simp [Matrix.reindex_apply]
  map_smul' c X := by
    ext i j
    simp [Matrix.reindex_apply]

theorem outputReindex_isCompletelyPositive
    (Phi : MatrixMap α β) (e : β ≃ γ)
    (hPhi : MatrixMap.IsCompletelyPositive Phi) :
    MatrixMap.IsCompletelyPositive (Phi.outputReindex e) := by
  change (MatrixMap.choi (Phi.outputReindex e)).PosSemidef
  have hchoi :
      MatrixMap.choi (Phi.outputReindex e) =
        (MatrixMap.choi Phi).submatrix
          (fun x : Prod α γ => (x.1, e.symm x.2))
          (fun x : Prod α γ => (x.1, e.symm x.2)) := by
    ext x y
    rfl
  rw [hchoi]
  exact hPhi.submatrix _

theorem outputReindex_isTracePreserving
    (Phi : MatrixMap α β) (e : β ≃ γ)
    (hPhi : MatrixMap.IsTracePreserving Phi) :
    MatrixMap.IsTracePreserving (Phi.outputReindex e) := by
  intro X
  change (Matrix.reindex e e (Phi X)).trace = X.trace
  rw [cMatrix_trace_reindex e, hPhi X]

theorem outputReindex_mapsPositive
    (Phi : MatrixMap α β) (e : β ≃ γ)
    (hPhi : ∀ X : CMatrix α, X.PosSemidef → (Phi X).PosSemidef) :
    ∀ X : CMatrix α, X.PosSemidef → ((Phi.outputReindex e) X).PosSemidef := by
  intro X hX
  change (Matrix.reindex e e (Phi X)).PosSemidef
  exact (hPhi X hX).submatrix e.symm

end MatrixMap

namespace MatrixMap

/-- Right-slice form of the Kronecker product of matrix maps.  It views
`(Φ ⊗ Ψ)(X)` as first applying `Φ` to each right-index slice of `X`, then
applying `Ψ` to the resulting right-index matrix. -/
theorem kron_apply_slice_right
    {a₀ : Type u} {b₀ : Type v} {a₁ : Type w} {b₁ : Type x}
    [Fintype a₀] [DecidableEq a₀] [Fintype b₀] [DecidableEq b₀]
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    (Φ : MatrixMap a₀ b₀) (Ψ : MatrixMap a₁ b₁) (X : CMatrix (Prod a₀ a₁))
    (x₀ y₀ : b₀) (x₁ y₁ : b₁) :
    MatrixMap.kron Φ Ψ X (x₀, x₁) (y₀, y₁) =
      Ψ (fun j j' => Φ (fun i i' => X (i, j) (i', j')) x₀ y₀) x₁ y₁ := by
  unfold MatrixMap.kron
  rw [map_eq_sum_single Ψ
    (fun j j' => Φ (fun i i' => X (i, j) (i', j')) x₀ y₀)]
  simp only [Matrix.sum_apply]
  have hΦ : ∀ j j',
      Φ (fun i i' => X (i, j) (i', j')) x₀ y₀ =
        ∑ i : a₀, ∑ i' : a₀,
          X (i, j) (i', j') * Φ (Matrix.single i i' (1 : Complex)) x₀ y₀ := by
    intro j j'
    have h := congrFun
      (congrFun (map_eq_sum_single Φ (fun i i' => X (i, j) (i', j'))) x₀)
      y₀
    simpa [Matrix.sum_apply] using h
  simp_rw [hΦ]
  simp [Finset.sum_mul, mul_assoc]

end MatrixMap

namespace Channel

variable {α : Type u} {β : Type v} {γ : Type w}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Fintype γ] [DecidableEq γ]

/-- Relabel the output basis of a finite-dimensional channel. -/
def outputReindex (Phi : Channel α β) (e : β ≃ γ) : Channel α γ where
  map := Phi.map.outputReindex e
  completelyPositive :=
    MatrixMap.outputReindex_isCompletelyPositive Phi.map e Phi.completelyPositive
  tracePreserving :=
    MatrixMap.outputReindex_isTracePreserving Phi.map e Phi.tracePreserving
  mapsPositive :=
    MatrixMap.outputReindex_mapsPositive Phi.map e Phi.mapsPositive

@[simp]
theorem outputReindex_applyState (Phi : Channel α β) (ρ : State α) (e : β ≃ γ) :
    (Phi.outputReindex e).applyState ρ = (Phi.applyState ρ).reindex e := by
  apply State.ext
  rfl

end Channel

namespace POVM

variable {α : Type u} {β : Type v} {m : Type w}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Fintype m] [DecidableEq m]

/-- Relabel the measured system of a finite POVM. -/
def reindex (M : POVM m α) (e : α ≃ β) : POVM m β where
  effects y := Matrix.reindex e e (M.effects y)
  pos y := (M.pos y).submatrix e.symm
  sum_eq_one := by
    ext i j
    have h := congrFun (congrFun M.sum_eq_one (e.symm i)) (e.symm j)
    simpa [Matrix.sum_apply, Matrix.reindex_apply, Matrix.one_apply] using h

omit [DecidableEq m] in
@[simp]
theorem reindex_effects (M : POVM m α) (e : α ≃ β) (y : m) :
    (M.reindex e).effects y = Matrix.reindex e e (M.effects y) :=
  rfl

/-- Born probabilities are invariant under simultaneous state/effect relabeling. -/
theorem prob_reindex_state (M : POVM m α) (ρ : State α) (e : α ≃ β) (y : m) :
    ((M.reindex e).prob (ρ.reindex e) y : ℝ) = (M.prob ρ y : ℝ) := by
  rw [POVM.prob_eq_trace_re, POVM.prob_eq_trace_re]
  change Complex.re
      (((Matrix.reindex e e ρ.matrix) *
        (Matrix.reindex e e (M.effects y))).trace) =
    Complex.re ((ρ.matrix * M.effects y).trace)
  change Complex.re
      ((((Matrix.reindexAlgEquiv ℂ ℂ e) ρ.matrix) *
        ((Matrix.reindexAlgEquiv ℂ ℂ e) (M.effects y))).trace) =
    Complex.re ((ρ.matrix * M.effects y).trace)
  rw [← Matrix.reindexAlgEquiv_mul (R := ℂ) (A := ℂ) e ρ.matrix (M.effects y)]
  change Complex.re ((Matrix.reindex e e (ρ.matrix * M.effects y)).trace) =
    Complex.re ((ρ.matrix * M.effects y).trace)
  rw [cMatrix_trace_reindex e]

end POVM

theorem state_reindex_reindex_symm {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ : State α) (e : α ≃ β) :
    (ρ.reindex e).reindex e.symm = ρ := by
  apply State.ext
  ext i j
  simp [State.reindex]

theorem state_reindex_symm_reindex {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ : State β) (e : α ≃ β) :
    (ρ.reindex e.symm).reindex e = ρ := by
  apply State.ext
  ext i j
  simp [State.reindex]

theorem cMatrix_rpow_reindex_nonneg {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (A : CMatrix α) (hA : A.PosSemidef)
    {s : ℝ} (hs0 : 0 ≤ s) :
    CFC.rpow (Matrix.reindex e e A) s =
      Matrix.reindex e e (CFC.rpow A s) := by
  change (Matrix.reindex e e A) ^ s = Matrix.reindex e e (A ^ s)
  have hmap_nonneg : 0 ≤ Matrix.reindex e e A := by
    exact Matrix.nonneg_iff_posSemidef.mpr (hA.submatrix e.symm)
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  rw [CFC.rpow_eq_cfc_real (a := Matrix.reindex e e A) (y := s) hmap_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s) hA_nonneg]
  simpa [cMatrixReindexStarAlgEquiv, Matrix.reindexAlgEquiv_apply] using
    (StarAlgHomClass.map_cfc
      (cMatrixReindexStarAlgEquiv e)
      (fun x : ℝ => x ^ s) A
      (hf := (Real.continuous_rpow_const hs0).continuousOn)
      (hφ := by
        change Continuous (Matrix.reindex e e : CMatrix α -> CMatrix β)
        fun_prop)).symm

namespace State

/-- Re-associate a product-channel output so that the second channel is the
right-local channel with reference `(R × B₁)`. -/
theorem applyState_id_prod_prod_assoc_symm
    {r : Type u} {a₁ : Type v} {b₁ : Type w} {a₂ : Type x} {b₂ : Type y}
    [Fintype r] [DecidableEq r]
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (N₁ : Channel a₁ b₁) (N₂ : Channel a₂ b₂)
    (ρ : State (Prod r (Prod a₁ a₂))) :
    (((Channel.idChannel r).prod (N₁.prod N₂)).applyState ρ).reindex
        (Equiv.prodAssoc r b₁ b₂).symm =
      (((Channel.idChannel (Prod r b₁)).prod N₂).applyState
        ((((Channel.idChannel r).prod (N₁.prod (Channel.idChannel a₂))).applyState ρ).reindex
          (Equiv.prodAssoc r b₁ a₂).symm)) := by
  apply State.ext
  ext x y
  rcases x with ⟨xRB1, xB2⟩
  rcases y with ⟨yRB1, yB2⟩
  rcases xRB1 with ⟨xR, xB1⟩
  rcases yRB1 with ⟨yR, yB1⟩
  simp only [Channel.applyState, Channel.prod, State.reindex_matrix,
    Matrix.submatrix_apply]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  simp [Equiv.prodAssoc]
  simp_rw [MatrixMap.kron_idChannel_left_apply_slice]
  change MatrixMap.kron N₁.map N₂.map
      (fun j j' => ρ.matrix (xR, j) (yR, j'))
      (xB1, xB2) (yB1, yB2) =
    N₂.map
      (fun j j' =>
        (MatrixMap.kron N₁.map (Channel.idChannel a₂).map
          (fun z z' => ρ.matrix (xR, z) (yR, z')))
          (xB1, j) (yB1, j'))
      xB2 yB2
  have hslice :
      (fun j j' =>
        (MatrixMap.kron N₁.map (Channel.idChannel a₂).map
          (fun z z' => ρ.matrix (xR, z) (yR, z')))
          (xB1, j) (yB1, j')) =
        (fun j j' =>
          N₁.map (fun i i' => ρ.matrix (xR, (i, j)) (yR, (i', j'))) xB1 yB1) := by
    ext j j'
    rw [MatrixMap.kron_idChannel_apply_slice]
  rw [hslice]
  exact MatrixMap.kron_apply_slice_right
    N₁.map N₂.map (fun j j' => ρ.matrix (xR, j) (yR, j'))
    xB1 yB1 xB2 yB2

/-- The `(R × B₁)` marginal of the partially processed state is the output of
`N₁` on the corresponding mixed `(R × A₁)` input. -/
theorem partialProductOutput_marginalAB
    {r : Type u} {a₁ : Type v} {b₁ : Type w} {a₂ : Type x}
    [Fintype r] [DecidableEq r]
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂]
    (N₁ : Channel a₁ b₁) (ρ : State (Prod r (Prod a₁ a₂))) :
    (((((Channel.idChannel r).prod (N₁.prod (Channel.idChannel a₂))).applyState ρ).reindex
          (Equiv.prodAssoc r b₁ a₂).symm).marginalAB) =
      ((Channel.idChannel r).prod N₁).applyState
        ((ρ.reindex (Equiv.prodAssoc r a₁ a₂).symm).marginalAB) := by
  apply State.ext
  ext x y
  rcases x with ⟨xR, xB1⟩
  rcases y with ⟨yR, yB1⟩
  simp only [State.marginalAB, State.marginalA, QIT.partialTraceB, State.reindex_matrix,
    Channel.applyState, Channel.prod, Matrix.submatrix_apply]
  simp [Equiv.prodAssoc]
  simp_rw [MatrixMap.kron_idChannel_left_apply_slice]
  change
    (∑ x_1 : a₂,
      (MatrixMap.kron N₁.map (Channel.idChannel a₂).map
        (fun j j' => ρ.matrix (xR, j) (yR, j')))
        (xB1, x_1) (yB1, x_1)) =
      N₁.map
        (fun j j' => ∑ x_1 : a₂, ρ.matrix (xR, (j, x_1)) (yR, (j', x_1)))
        xB1 yB1
  simp_rw [MatrixMap.kron_idChannel_apply_slice]
  have hsum :=
    congrFun
      (congrFun
        (map_sum N₁.map
          (fun x_1 : a₂ => fun i i' =>
            ρ.matrix (xR, (i, x_1)) (yR, (i', x_1)))
          Finset.univ)
        xB1)
      yB1
  simp only [Matrix.sum_apply] at hsum
  have hmatrix :
      (fun j j' => ∑ x_1 : a₂, ρ.matrix (xR, (j, x_1)) (yR, (j', x_1))) =
        (∑ x_1 : a₂, fun i i' => ρ.matrix (xR, (i, x_1)) (yR, (i', x_1))) := by
    ext j j'
    simp
  rw [hmatrix]
  exact hsum.symm

theorem mutualInformation_bipartiteProduct
    {a₁ : Type u} {b₁ : Type v} {a₂ : Type w} {b₂ : Type x}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ : State (Prod a₁ b₁)) (σ : State (Prod a₂ b₂)) :
    mutualInformation (ρ.bipartiteProduct σ) =
      mutualInformation ρ + mutualInformation σ := by
  unfold mutualInformation
  rw [State.bipartiteProduct_marginalA, State.bipartiteProduct_marginalB]
  rw [State.vonNeumann_prod, State.vonNeumann_prod]
  unfold State.bipartiteProduct
  rw [State.vonNeumann_reindex, State.vonNeumann_prod]
  ring

/-- Chain-rule form used for the channel mutual-information additivity upper
bound:
`I(R;B₁B₂) = I(R;B₁) + I(RB₁;B₂) - I(B₁;B₂)`.

The state is stored as `(R × B₁) × B₂`; the left side re-associates it as
`R × (B₁ × B₂)`.
This follows the source route in Khatri--Wilde,
`Chapters/EA_capacity.tex`, lines 1080-1086. -/
theorem mutualInformation_assoc_chain
    {r : Type u} {b₁ : Type v} {b₂ : Type w}
    [Fintype r] [DecidableEq r] [Fintype b₁] [DecidableEq b₁]
    [Fintype b₂] [DecidableEq b₂]
    (ρ : State (Prod (Prod r b₁) b₂)) :
    mutualInformation (ρ.reindex (Equiv.prodAssoc r b₁ b₂)) =
      mutualInformation ρ.marginalAB + mutualInformation ρ -
        mutualInformation ρ.marginalBC := by
  unfold mutualInformation
  have hA :
      (ρ.reindex (Equiv.prodAssoc r b₁ b₂)).marginalA =
        ρ.marginalAB.marginalA := by
    apply State.ext
    ext x y
    simp [State.reindex, State.marginalA, State.marginalAB, QIT.partialTraceB,
      Equiv.prodAssoc, Fintype.sum_prod_type]
  have hB :
      (ρ.reindex (Equiv.prodAssoc r b₁ b₂)).marginalB =
        ρ.marginalBC := by
    apply State.ext
    ext x y
    simp [State.reindex, State.marginalB, State.marginalBC, QIT.partialTraceA,
      Equiv.prodAssoc]
  rw [hA, hB, State.vonNeumann_reindex]
  rw [State.marginalAB_eq_marginalA]
  rw [State.marginalBC_marginalA_eq_marginalBOfABC,
    State.marginalBC_marginalB_eq_marginalB]
  rw [State.marginalBOfABC_eq, State.marginalAB_eq_marginalA]
  ring

/-- Chain-rule upper bound obtained from
`I(R;B₁B₂) = I(R;B₁) + I(RB₁;B₂) - I(B₁;B₂)` and nonnegativity of
mutual information. -/
theorem mutualInformation_assoc_le
    {r : Type u} {b₁ : Type v} {b₂ : Type w}
    [Fintype r] [DecidableEq r] [Fintype b₁] [DecidableEq b₁]
    [Fintype b₂] [DecidableEq b₂]
    (ρ : State (Prod (Prod r b₁) b₂)) :
    mutualInformation (ρ.reindex (Equiv.prodAssoc r b₁ b₂)) ≤
      mutualInformation ρ.marginalAB + mutualInformation ρ := by
  rw [State.mutualInformation_assoc_chain]
  have hnonneg : 0 ≤ mutualInformation ρ.marginalBC :=
    State.mutualInformation_nonneg ρ.marginalBC
  linarith

/-- Mutual information is additive on IID bipartite tensor powers:
`I(A^n;B^n)_{ρ^{⊗n}} = n I(A;B)_ρ`. -/
theorem mutualInformation_tensorPowerBipartite (ρ : State (Prod a b)) (n : ℕ) :
    mutualInformation (ρ.tensorPowerBipartite n) =
      (n : ℝ) * mutualInformation ρ := by
  unfold mutualInformation
  rw [ρ.tensorPowerBipartite_marginalA n,
    ρ.tensorPowerBipartite_marginalB n]
  rw [State.vonNeumann_tensorPower,
    State.vonNeumann_tensorPower,
    show vonNeumann (ρ.tensorPowerBipartite n) =
      vonNeumann ((ρ.tensorPower n).reindex (tensorPowerProdEquiv a b n)) from rfl,
    State.vonNeumann_reindex,
    State.vonNeumann_tensorPower]
  ring

/-- PSD-domain Petz--Renyi divergence is invariant under simultaneous finite
basis relabeling in the source range `0 <= alpha <= 1`. -/
theorem petzRenyiPSDFinite_reindex {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ σ : State α) (e : α ≃ β)
    (alphaR : ℝ) (halpha_pos : 0 < alphaR) (halpha_lt_one : alphaR < 1) :
    (ρ.reindex e).petzRenyiPSDFinite (σ.reindex e)
        alphaR halpha_pos (ne_of_lt halpha_lt_one) =
      ρ.petzRenyiPSDFinite σ alphaR halpha_pos (ne_of_lt halpha_lt_one) := by
  unfold State.petzRenyiPSDFinite
  have halpha_nonneg : 0 ≤ alphaR := le_of_lt halpha_pos
  have hone_sub_nonneg : 0 ≤ 1 - alphaR := sub_nonneg.mpr (le_of_lt halpha_lt_one)
  rw [State.reindex_matrix, State.reindex_matrix]
  change (1 / (alphaR - 1)) *
      log2 (((CFC.rpow (Matrix.reindex e e ρ.matrix) alphaR *
        CFC.rpow (Matrix.reindex e e σ.matrix) (1 - alphaR)).trace).re) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow ρ.matrix alphaR *
        CFC.rpow σ.matrix (1 - alphaR)).trace).re)
  rw [cMatrix_rpow_reindex_nonneg e ρ.matrix ρ.pos halpha_nonneg]
  rw [cMatrix_rpow_reindex_nonneg e σ.matrix σ.pos hone_sub_nonneg]
  change (1 / (alphaR - 1)) *
      log2 ((((Matrix.reindexAlgEquiv ℂ ℂ e) (CFC.rpow ρ.matrix alphaR) *
        (Matrix.reindexAlgEquiv ℂ ℂ e)
          (CFC.rpow σ.matrix (1 - alphaR))).trace).re) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow ρ.matrix alphaR *
        CFC.rpow σ.matrix (1 - alphaR)).trace).re)
  rw [← Matrix.reindexAlgEquiv_mul (R := ℂ) (A := ℂ) e
    (CFC.rpow ρ.matrix alphaR) (CFC.rpow σ.matrix (1 - alphaR))]
  change (1 / (alphaR - 1)) *
      log2 (((Matrix.reindex e e
        (CFC.rpow ρ.matrix alphaR *
          CFC.rpow σ.matrix (1 - alphaR))).trace).re) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow ρ.matrix alphaR *
        CFC.rpow σ.matrix (1 - alphaR)).trace).re)
  rw [cMatrix_trace_reindex e]

/-- The product-marginal Petz coefficient is strictly positive in the source
range `0 < alpha < 1`, because the product-marginal Nussbaum--Szkola model has
nonempty common support. -/
theorem petzRenyiCoefficient_productMarginal_pos
    (ρ : State (Prod a b)) {alphaR : ℝ}
    (halpha_pos : 0 < alphaR) (halpha_lt_one : alphaR < 1) :
    0 < ρ.petzRenyiCoefficient (ρ.marginalA.prod ρ.marginalB) alphaR := by
  classical
  let M := BinaryHypothesisTest.productMarginalNussbaumSzkolaModel ρ
  have hpq : M.pDistribution.SupportedBy M.q := by
    simpa [M] using
      BinaryHypothesisTest.productMarginalNussbaumSzkolaModel_p_supportedBy_q ρ
  have hcommon :
      Nonempty M.commonSupport :=
    BinaryHypothesisTest.ClassicalBinaryModel.commonSupport_nonempty_of_p_supportedBy_q
      (M := M) hpq
  have hpart_pos : 0 < M.chernoffPartitionNNReal alphaR :=
    BinaryHypothesisTest.ClassicalBinaryModel.chernoffPartitionNNReal_pos_of_commonSupport_nonempty
      (M := M) hcommon alphaR
  have hpart :
      M.chernoffPartitionNNReal alphaR = M.petzChernoffCoefficient alphaR :=
    BinaryHypothesisTest.ClassicalBinaryModel.chernoffPartitionNNReal_eq_petzChernoffCoefficient_of_mem_Ioo
      (M := M) halpha_pos halpha_lt_one
  have hcoeff :
      M.petzChernoffCoefficient alphaR =
        ρ.petzRenyiCoefficient (ρ.marginalA.prod ρ.marginalB) alphaR := by
    simpa [M] using
      BinaryHypothesisTest.productMarginalNussbaumSzkolaModel_petzChernoffCoefficient_eq
        ρ (le_of_lt halpha_pos) (le_of_lt halpha_lt_one)
  simpa [hpart, hcoeff] using hpart_pos

/-- PSD-domain Petz--Renyi divergence is additive on IID tensor powers when
the base coefficient is positive. -/
theorem petzRenyiPSDFinite_tensorPower
    {α : Type u} [Fintype α] [DecidableEq α] (ρ σ : State α)
    {alphaR : ℝ} (halpha_pos : 0 < alphaR) (halpha_lt_one : alphaR < 1)
    (hcoeff : 0 < ρ.petzRenyiCoefficient σ alphaR) (n : ℕ) :
    (ρ.tensorPower n).petzRenyiPSDFinite (σ.tensorPower n)
        alphaR halpha_pos (ne_of_lt halpha_lt_one) =
      (n : ℝ) * ρ.petzRenyiPSDFinite σ alphaR halpha_pos (ne_of_lt halpha_lt_one) := by
  unfold State.petzRenyiPSDFinite
  have halpha_nonneg : 0 ≤ alphaR := le_of_lt halpha_pos
  have halpha_le_one : alphaR ≤ 1 := le_of_lt halpha_lt_one
  have htrace_tensor :
      ((CFC.rpow (ρ.tensorPower n).matrix alphaR *
          CFC.rpow (σ.tensorPower n).matrix (1 - alphaR)).trace).re =
        ((ρ.petzRenyiCoefficient σ alphaR : ℝ) ^ n) := by
    have htrace :
        ((CFC.rpow (ρ.tensorPower n).matrix alphaR *
            CFC.rpow (σ.tensorPower n).matrix (1 - alphaR)).trace).re =
          (((ρ.tensorPower n).petzRenyiCoefficient (σ.tensorPower n) alphaR : ℝ)) := by
      have h := State.petzRenyiCoefficient_trace_eq
        (ρ.tensorPower n) (σ.tensorPower n) alphaR
      have hre := congrArg Complex.re h
      simpa using hre.symm
    have hcoeff_tensor :
        (((ρ.tensorPower n).petzRenyiCoefficient
            (σ.tensorPower n) alphaR : ℝ) =
          ((ρ.petzRenyiCoefficient σ alphaR : ℝ) ^ n)) := by
      exact_mod_cast State.petzRenyiCoefficient_tensorPower
        ρ σ halpha_nonneg halpha_le_one n
    rw [htrace, hcoeff_tensor]
  have htrace_base :
      ((CFC.rpow ρ.matrix alphaR *
          CFC.rpow σ.matrix (1 - alphaR)).trace).re =
        (ρ.petzRenyiCoefficient σ alphaR : ℝ) := by
    have h := State.petzRenyiCoefficient_trace_eq ρ σ alphaR
    have hre := congrArg Complex.re h
    simpa using hre.symm
  change (1 / (alphaR - 1)) *
      log2 ((CFC.rpow (ρ.tensorPower n).matrix alphaR *
        CFC.rpow (σ.tensorPower n).matrix (1 - alphaR)).trace).re =
    (n : ℝ) *
      ((1 / (alphaR - 1)) *
        log2 ((CFC.rpow ρ.matrix alphaR *
          CFC.rpow σ.matrix (1 - alphaR)).trace).re)
  rw [htrace_tensor, htrace_base]
  have hcoeff_real_pos : 0 < (ρ.petzRenyiCoefficient σ alphaR : ℝ) := by
    exact_mod_cast hcoeff
  rw [log2_pow_nat (ρ.petzRenyiCoefficient σ alphaR : ℝ) n]
  ring

/-- PSD-domain barred Petz--Renyi mutual information is additive on IID
bipartite tensor powers. -/
theorem barPetzRenyiMutualInformationPSDFinite_tensorPowerBipartite
    (ρ : State (Prod a b)) {alphaR : ℝ}
    (halpha_pos : 0 < alphaR) (halpha_lt_one : alphaR < 1) (n : ℕ) :
    (ρ.tensorPowerBipartite n).barPetzRenyiMutualInformationPSDFinite
        alphaR halpha_pos (ne_of_lt halpha_lt_one) =
      (n : ℝ) *
        ρ.barPetzRenyiMutualInformationPSDFinite
          alphaR halpha_pos (ne_of_lt halpha_lt_one) := by
  have hcomp :
      (ρ.tensorPowerBipartite n).marginalA.prod
          (ρ.tensorPowerBipartite n).marginalB =
        (ρ.marginalA.prod ρ.marginalB).tensorPowerBipartite n := by
    calc
      (ρ.tensorPowerBipartite n).marginalA.prod
          (ρ.tensorPowerBipartite n).marginalB =
        (ρ.marginalA.tensorPower n).prod
          (ρ.marginalB.tensorPower n) := by
          rw [ρ.tensorPowerBipartite_marginalA n,
            ρ.tensorPowerBipartite_marginalB n]
      _ = (ρ.marginalA.prod ρ.marginalB).tensorPowerBipartite n :=
          (State.prod_tensorPowerBipartite ρ.marginalA ρ.marginalB n).symm
  unfold State.barPetzRenyiMutualInformationPSDFinite
  calc
    (ρ.tensorPowerBipartite n).petzRenyiPSDFinite
        ((ρ.tensorPowerBipartite n).marginalA.prod
          (ρ.tensorPowerBipartite n).marginalB)
        alphaR halpha_pos (ne_of_lt halpha_lt_one) =
      (ρ.tensorPowerBipartite n).petzRenyiPSDFinite
        ((ρ.marginalA.prod ρ.marginalB).tensorPowerBipartite n)
        alphaR halpha_pos (ne_of_lt halpha_lt_one) := by
        unfold State.petzRenyiPSDFinite
        rw [congrArg State.matrix hcomp]
    _ =
      (n : ℝ) *
        ρ.petzRenyiPSDFinite (ρ.marginalA.prod ρ.marginalB)
          alphaR halpha_pos (ne_of_lt halpha_lt_one) := by
        change
          ((ρ.tensorPower n).reindex (tensorPowerProdEquiv a b n)).petzRenyiPSDFinite
            (((ρ.marginalA.prod ρ.marginalB).tensorPower n).reindex
              (tensorPowerProdEquiv a b n))
            alphaR halpha_pos (ne_of_lt halpha_lt_one) =
          (n : ℝ) *
            ρ.petzRenyiPSDFinite (ρ.marginalA.prod ρ.marginalB)
              alphaR halpha_pos (ne_of_lt halpha_lt_one)
        rw [State.petzRenyiPSDFinite_reindex
          (ρ.tensorPower n)
          ((ρ.marginalA.prod ρ.marginalB).tensorPower n)
          (tensorPowerProdEquiv a b n)
          alphaR halpha_pos halpha_lt_one]
        exact State.petzRenyiPSDFinite_tensorPower ρ
          (ρ.marginalA.prod ρ.marginalB)
          halpha_pos halpha_lt_one
          (State.petzRenyiCoefficient_productMarginal_pos
            ρ halpha_pos halpha_lt_one)
          n

end State

end

end QIT
